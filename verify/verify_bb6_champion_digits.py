"""Standalone verifier: the last D decimal digits of the BB(6) champion's halting step count.

Machine 1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE (mxdys, 2025). Python standard library only.

Rules (BusyBeaverWiki page of this machine), with configuration S1(L, N, m, a, b):
    Inc_m : S1(L, N+1, m, a, b) -> S1(L, N, m-1 mod 3, a+b+d_m, 2^b-1),  d_0 = 1, d_1 = d_2 = 2
    Rst1  : S1(L, 0, 1, a, b)   -> S1(L+a+2, (2^(L+2)-1)*2^a - 1, 2, b, 2^b-1)
    Rst0  : S1(L, 0, 0, a, b)   -> halt
    start : S1(3, 7, 2, 6, 63)
Step costs carried explicitly and each one checked here against the 12-row machine on small instances:
    Inc   : 6c'^2 + 54c' + 12a + 4m - 9b + 63 + 12*nu2(N+1),   c' = 2^b - 1
    Rst1  : 6s^2 + 54s + 12L + 12a - 9b + 97,                s = 2^b - 1
    Rst0  : 12L + 12a + 60  (the halting transition included)
    blank tape -> S1(3, 7, 2, 6, 63) in 27,965 steps
S1 tape, head on the last cell of the left word, state E:
    left  = 111011 . C(L, N) . 100 . 10 . 1^m . 1^(3a)      C(width, v): binary v, 1 -> 100, 0 -> 111, zero-padded
    right = 011100 . (111)^(b+1)

A phase is N Inc steps followed by Rst1 or Rst0; its cost is summed in closed form (derived below, and
checked against step-by-step sums) and every count is held as an exact expression whose residues modulo
any modulus are computed with Carmichael exponent reduction. Nothing tower-sized is expanded.

    python3 verify_bb6_champion_digits.py [--digits 200]
"""
import sys
from functools import lru_cache
from math import gcd

TABLE = '1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE'
BRIDGE = 27965


# ---------- the 12-row machine and the S1 tape ----------

def rules():
    out = {}
    for q, block in zip('ABCDEF', TABLE.split('_')):
        for bit in (0, 1):
            w, d, t = block[3 * bit:3 * bit + 3]
            out[(q, bit)] = (int(w), 1 if d == 'R' else -1, t)
    return out


RULES = rules()


def counter_word(width, value):
    digits = bin(value)[2:] if value else ''
    assert len(digits) <= width
    return '1' * (3 * (width - len(digits))) + ''.join('100' if c == '1' else '111' for c in digits)


def s1_tape(L, N, m, a, b):
    left = '111011' + counter_word(L, N) + '100' + '10' + '1' * m + '1' * (3 * a)
    right = '011100' + '111' * (b + 1)
    ones = {k - (len(left) - 1) for k, c in enumerate(left) if c == '1'}
    ones |= {k + 1 for k, c in enumerate(right) if c == '1'}
    return frozenset(ones)


def first_reach(ones, state, target, budget):
    """Steps until the machine first shows target (ones relative to the head) in state E, or halts."""
    ones, head = set(ones), 0
    for t in range(1, budget + 1):
        w, d, nxt = RULES[(state, int(head in ones))]
        (ones.add if w else ones.discard)(head)
        if nxt == 'Z':
            return ('halt', t)
        head += d
        state = nxt
        if target is not None and state == 'E' and frozenset(x - head for x in ones) == target:
            return ('reach', t)
    return ('budget', budget)


def nu2(n):
    return (n & -n).bit_length() - 1


def inc_cost(N, m, a, b):
    c1 = 2 ** b - 1
    return 6 * c1 * c1 + 54 * c1 + 12 * a + 4 * m - 9 * b + 63 + 12 * nu2(N)


def d_of(m):
    return 1 if m == 0 else 2


def check_costs():
    """Every cost law against the machine itself."""
    checks = 0
    blank = first_reach((), 'A', s1_tape(3, 7, 2, 6, 63), 40000)
    assert blank == ('reach', BRIDGE), blank
    checks += 1
    for L in range(1, 4):
        for N in range(1, 2 ** L):
            for m in range(3):
                for a in range(4):
                    for b in range(4):
                        target = s1_tape(L, N - 1, (m - 1) % 3, a + b + d_of(m), 2 ** b - 1)
                        got = first_reach(s1_tape(L, N, m, a, b), 'E', target, 200000)
                        assert got == ('reach', inc_cost(N, m, a, b)), (L, N, m, a, b, got)
                        checks += 1
    for L in range(1, 3):
        for a in range(4):
            for b in range(4):
                s = 2 ** b - 1
                target = s1_tape(L + a + 2, (2 ** (L + 2) - 1) * 2 ** a - 1, 2, b, s)
                got = first_reach(s1_tape(L, 0, 1, a, b), 'E', target, 200000)
                assert got == ('reach', 6 * s * s + 54 * s + 12 * L + 12 * a - 9 * b + 97), (L, a, b, got)
                checks += 1
                got = first_reach(s1_tape(L, 0, 0, a, b), 'E', None, 200000)
                assert got == ('halt', 12 * L + 12 * a + 60), (L, a, b, got)
                checks += 1
    return checks


# ---------- exact expressions and their residues ----------

def factor(n):
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1 if p == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


@lru_cache(maxsize=None)
def carmichael(n):
    lam = 1
    for p, e in factor(n).items():
        v = p ** (e - 1) * (p - 1) if p > 2 else (1 if e == 1 else 2 if e == 2 else 2 ** (e - 2))
        lam = lam * v // gcd(lam, v)
    return lam


@lru_cache(maxsize=None)
def chain(m):
    out = [m]
    while out[-1] > 1:
        o = out[-1]
        while o % 2 == 0:
            o //= 2
        out.append(carmichael(o) if o > 1 else 1)
    return tuple(out)


def split2(m):
    s = 0
    while m % 2 == 0:
        m //= 2
        s += 1
    return s, m


def crt2(s, odd, r_odd):
    t = 1 << s
    if odd == 1:
        return 0
    return (t * ((r_odd * pow(t, -1, odd)) % odd)) % (t * odd)


HUGE = 1 << 64


def E(kind, *args):
    return (kind,) + args


def lb(x):
    """A lower bound, capped at HUGE."""
    k = x[0]
    if k == 'int':
        return min(x[1], HUGE)
    if k == 'add':
        return min(sum(lb(y) for y in x[1:]), HUGE)
    if k == 'mul':
        return min(lb(x[1]) * lb(x[2]), HUGE)
    if k == 'pow2':
        e = lb(x[1])
        return HUGE if e >= 64 else 1 << e
    if k == 'tower':
        h, base = lb(x[1]), lb(x[2])
        v = base
        for _ in range(min(h, 8)):
            v = HUGE if v >= 64 else (1 << v) - 1
        return v
    return 0


@lru_cache(maxsize=None)
def tower_res(base, h, m):
    """T^h(base) mod m for an exact small h, T(x) = 2^x - 1; exponents are known to exceed the 2-part."""
    if m == 1:
        return 0
    if h == 0:
        return res(base, m)
    prev = E('tower', E('int', h - 1), base)
    s, odd = split2(m)
    if lb(prev) < s + 1:
        exact = exact_value(E('tower', E('int', h), base))
        return exact % m
    r_odd = pow(2, tower_res(base, h - 1, carmichael(odd)) if odd > 1 else 0, odd) if odd > 1 else 0
    return (crt2(s, odd, r_odd) - 1) % m


def exact_value(x):
    k = x[0]
    if k == 'int':
        return x[1]
    if k == 'tower':
        v = exact_value(x[2])
        for _ in range(exact_value(x[1])):
            v = 2 ** v - 1
        return v
    raise ValueError(x)


def stable(m):
    return len(chain(m)) + 3


@lru_cache(maxsize=None)
def res(x, m):
    if m == 1:
        return 0
    k = x[0]
    if k == 'int':
        return x[1] % m
    if k == 'add':
        return sum(res(y, m) for y in x[1:]) % m
    if k == 'neg':
        return (-res(x[1], m)) % m
    if k == 'mul':
        return res(x[1], m) * res(x[2], m) % m
    if k == 'pow2':
        e = x[1]
        s, odd = split2(m)
        if lb(e) <= s + 1:
            return pow(2, exact_value(e) if e[0] == 'int' else res(e, carmichael(m) * m), m)
        r_odd = pow(2, res(e, carmichael(odd)), odd) if odd > 1 else 0
        return crt2(s, odd, r_odd)
    if k == 'tower':
        h, base = x[1], x[2]
        I = stable(m)
        if h[0] == 'int' and h[1] <= I:
            return tower_res(base, h[1], m)
        return tower_res(base, I, m)
    if k == 'tsum':
        h, base, p, start = x[1], x[2], x[3], x[4]
        I = stable(m)
        terms = [pow(res(E('tower', E('int', start + i), base), m), p, m) for i in range(I)]
        if h[0] == 'int' and h[1] <= I:
            return sum(terms[:h[1]]) % m
        c = pow(res(E('tower', E('int', start + I), base), m), p, m)
        return (sum(terms) + (res(h, m) - I) * c) % m
    if k == 'wsum':
        h, base = x[1], x[2]
        I = stable(m)
        terms = [res(E('tower', E('int', i), base), m) for i in range(I)]
        if h[0] == 'int' and h[1] <= I:
            n = h[1]
            return sum((n - 1 - i) * terms[i] for i in range(n)) % m
        c = res(E('tower', E('int', I), base), m)
        hm = res(h, m)
        head = sum((hm - 1 - i) * t for i, t in enumerate(terms))
        u = (res(h, 2 * m) - I) % (2 * m)
        return (head + c * (u * (u - 1) // 2)) % m
    if k == 'div':
        n, q = x[1], x[2]
        return (res(n, q * m) // q) % m
    raise ValueError(k)


def I_(v):
    return E('int', v)


def add(*xs):
    return E('add', *xs)


def neg(x):
    return E('neg', x)


def mul(a, b):
    return E('mul', a, b)


def sc(k, x):
    return E('mul', I_(k), x)


# ---------- one phase in closed form ----------

def phase(L, N, m, a, b, popN, nmod3):
    """N Inc steps from S1(L, N, m, a, b). Returns (bulk cost, a', b', mode') as expressions."""
    r = nmod3
    q = E('div', add(N, I_(-r)), 3)
    count = [add(q, I_(1 if s < r else 0)) for s in range(3)]
    tw_sq = E('tsum', N, b, 2, 1)
    tw_1 = E('tsum', N, b, 1, 1)
    tw_0 = E('tsum', N, b, 1, 0)
    tw_w = E('wsum', N, b)
    sum_m = add(sc(3, q), I_(sum((m - j) % 3 for j in range(r))))
    weighted_d = []
    for s in range(3):
        cs = count[s]
        weighted_d.append(sc(d_of((m - s) % 3), add(mul(cs, add(N, I_(-1 - s))),
                                                     neg(sc(3, E('div', mul(cs, add(cs, I_(-1))), 2))))))
    cost = add(sc(6, tw_sq), sc(54, tw_1), neg(sc(9, tw_0)), sc(12, mul(N, a)), sc(12, tw_w), sc(12, add(*weighted_d)),
               sc(4, sum_m), sc(63, N), sc(12, add(N, neg(popN))))
    a2 = add(a, tw_0, add(*[sc(d_of((m - s) % 3), count[s]) for s in range(3)]))
    b2 = E('tower', N, b)
    return cost, a2, b2, (m - r) % 3


def check_phase_formula():
    """Closed-form phase cost and state against step-by-step sums of the Inc law."""
    checks = 0
    for b, top in ((0, 12), (1, 12), (2, 4), (3, 3)):
        for N in range(0, top + 1):
            for m in range(3):
                for a in range(3):
                    L = max(1, N.bit_length())
                    cost, a2, b2, m2 = phase(I_(L), I_(N), m, I_(a), I_(b), I_(bin(N).count('1')), N % 3)
                    tot, aa, bb, mm = 0, a, b, m
                    for k in range(N, 0, -1):
                        tot += inc_cost(k, mm, aa, bb)
                        aa, bb, mm = aa + bb + d_of(mm), 2 ** bb - 1, (mm - 1) % 3
                    for mod in (97, 10 ** 6, 2 ** 20):
                        assert res(cost, mod) == tot % mod, ('cost', N, m, a, b, mod)
                        assert res(a2, mod) == aa % mod and m2 == mm, ('state', N, m, a, b, mod)
                        assert res(b2, mod) == bb % mod, ('b', N, m, a, b, mod)
                    checks += 1
    return checks


# ---------- the champion ----------

def tau_residue(mod):
    L, N, m, a, b = I_(3), I_(7), 2, I_(6), I_(63)
    popN, nmod3 = I_(3), 1
    total = I_(BRIDGE)
    path = []
    for _ in range(64):
        cost, a2, b2, m2 = phase(L, N, m, a, b, popN, nmod3)
        total = add(total, cost)
        if m2 == 0:
            total = add(total, sc(12, L), sc(12, a2), I_(60))
            path.append('Rst0')
            return res(total, mod), path
        if m2 != 1:
            raise AssertionError('a phase ended in mode 2, outside the published rule path')
        s = E('tower', I_(1), b2)
        total = add(total, sc(6, mul(s, s)), sc(54, s), sc(12, L), sc(12, a2), neg(sc(9, b2)), I_(97))
        path.append('Rst1')
        x = add(L, I_(2))
        L, a, b, m = add(L, a2, I_(2)), b2, s, 2
        N = add(E('pow2', add(x, a2)), neg(E('pow2', a2)), I_(-1))
        popN = add(x, I_(-1), a2)
        nmod3 = res(N, 3)
    raise AssertionError('no halt within 64 phases')


def main():
    digits = int(sys.argv[sys.argv.index('--digits') + 1]) if '--digits' in sys.argv else 200
    n1 = check_costs()
    print(f'cost laws checked against the 12-row machine: {n1} cases (bridge {BRIDGE} steps, Inc, Rst1, Rst0)')
    n2 = check_phase_formula()
    print(f'closed-form phase sums checked against step-by-step sums: {n2} cases')
    r6, path = tau_residue(10 ** 6)
    print(f'phases: {path}')
    print(f'tau mod 10^6 = {r6}  (published elsewhere: 641105)')
    r, _ = tau_residue(10 ** digits)
    print(f'last {digits} decimal digits of tau:')
    print(str(r).zfill(digits))
    return 0 if r6 == 641105 else 1


if __name__ == '__main__':
    sys.exit(main())
