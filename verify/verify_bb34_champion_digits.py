"""Standalone verifier: the last D decimal digits of the BB(3,4) champion's halting step count and score.

Machine 1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC (Kropitz 2024; rules Ligocki, sligocki.com 2024-05-22). Python standard
library only. The twelve rows are an argument (--rows); every rule below is checked on the machine built from them.

Configuration B(k, n, a) = 0^inf 3^(a+1) 2^k A> 1^n followed by a right context (a is twice Ligocki's m).
    k = 1     : B(1, n+1, a) -> B(1, n, a+2)                   in 4a + 9 steps
    k = j + 2 : B(k, n+1, a) -> B(k, n, g_j(a))                in (2k+1) a + 4k + 3 + [steps of B(k-1, a+2, 0) -> B(k-1, 0, .)]
    g_0(a) = 2a + 4,  g_(j+1)(a) = g_j^(a+2)(0),  g_j(a) = 2^(j)(a + 4) - 4  (Knuth arrows, 2^(0) y = 2y)
    blank tape -> B(16, 3, 0) with context 2 at step 241;  B(k, 0, a) with context 2 halts in 1 step (A2 = 1RZ)
Clock:
    W1(n, a) = n (4a + 4n + 5)                                             n units at k = 1
    T_0(n, a) = sum_(i<n) C1(a_i),  C1(a) = 4a^2 + 26a + 37,  a_(i+1) = g_0(a_i)        (k = 2)
    T_(j+1)(n, a) = sum_(i<n) [C2(a_i, j) + T_j(a_i + 2, 0)],  C2(a, j) = (2j+7) a + 4j + 15,  a_(i+1) = g_(j+1)(a_i)
    tau = 241 + T_14(3, 0) + 1,   sigma = g_14^3(0) + 18 (nonblank cells of the halted tape)

Residues mod M = 10^D. With N = 2^^h - 2:  3 T_0(N, 0) + 72 2^N + 9N = 64 4^N + 8, read with the inverse of 3 and
2^N, 4^N by exponent reduction (2^x mod 2^a 5^(b+1) depends on x mod 4 5^b for x >= a); 2^^h mod 2^a 5^b is one
constant for h >= b + 6.  T_1(N, 0) is its first D + 4 summands and one repeating summand; T_(k+1)(N, 0) is one or two
first summands and one repeating summand of level k.  tau needs T_13 at 2^^2 - 2 = 2 and at a tall tower.

    python3 verify_bb34_champion_digits.py [--digits 200] [--rows 1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC]
"""
import sys
from functools import lru_cache

sys.setrecursionlimit(100000)
ROWS = '1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC'
ENTRY = 241


# ---------- the machine ----------

def parse(rows):
    out = {}
    for q, block in zip('ABC', rows.split('_')):
        for sym in range(4):
            w, d, t = block[3 * sym:3 * sym + 3]
            out[(q, sym)] = (int(w), 1 if d == 'R' else -1, t)
    return out


def run(rules, tape, head, state, steps):
    """`steps` steps (fewer if the machine halts); returns (steps taken, state, tape, head)."""
    tape = dict(tape)
    for t in range(steps):
        w, d, nxt = rules[(state, tape.get(head, 0))]
        tape[head] = w
        head += d
        if nxt == 'Z':
            return t + 1, 'Z', tape, head
        state = nxt
    return steps, state, tape, head


def b_config(k, n, a, context):
    """B(k, n, a) with the given right context: (tape, head), head on the first cell right of the 2-block."""
    cells = [3] * (a + 1) + [2] * k + [1] * n + list(context)
    head = a + 1 + k
    return {i: s for i, s in enumerate(cells) if s}, head


def same(tape1, head1, tape2, head2):
    return ({i - head1: s for i, s in tape1.items() if s} == {i - head2: s for i, s in tape2.items() if s})


# ---------- the clock on stored integers ----------

def g(j, a):
    if j == 0:
        return 2 * a + 4
    y = 0
    for _ in range(a + 2):
        y = g(j - 1, y)
    return y


def W1(n, a):
    return n * (4 * a + 4 * n + 5)


def C1(a):
    return 4 * a * a + 26 * a + 37


def C2(a, j):
    return (2 * j + 7) * a + 4 * j + 15


def T(j, n, a):
    total = 0
    for _ in range(n):
        total += C1(a) if j == 0 else C2(a, j - 1) + T(j - 1, a + 2, 0)
        a = g(j, a)
    return total


def cost(k, n, a):
    return W1(n, a) if k == 1 else T(k - 2, n, a)


def result(k, n, a):
    if k == 1:
        return a + 2 * n
    for _ in range(n):
        a = g(k - 2, a)
    return a


def check_machine(rules):
    """Each rule on the machine: (passed, total, lines)."""
    lines, ok, tot = [], 0, 0
    steps, state, tape, head = run(rules, {}, 0, 'A', ENTRY)
    want, wh = b_config(16, 3, 0, [2])
    e = steps == ENTRY and state == 'A' and same(tape, head, want, wh)
    lines.append(f'blank tape at step {ENTRY} is B(16, 3, 0) with context 2: {e}')
    cases = [(1, n, a) for n in range(1, 6) for a in range(0, 9, 2)]
    cases += [(2, n, a) for n in range(1, 4) for a in range(0, 7, 2)] + [(3, 1, 0), (3, 1, 2), (3, 2, 0), (4, 1, 0)]
    for context in ([2], [3, 1, 1, 2]):
        for k, n, a in cases:
            c = cost(k, n, a)
            if c > 3_000_000:
                continue
            tape, head = b_config(k, n, a, context)
            steps, state, tape, head = run(rules, tape, head, 'A', c)
            want, wh = b_config(k, 0, result(k, n, a), context)
            tot += 1
            ok += int(steps == c and state == 'A' and same(tape, head, want, wh))
    lines.append(f'B(k, n, a) -> B(k, 0, g^n(a)) at exactly the clock\'s step count, two right contexts: {ok}/{tot}')
    hk, ht = 0, 0
    for k, a in ((1, 0), (2, 6), (16, 0), (3, 4)):
        tape, head = b_config(k, 0, a, [2])
        steps, state, tape, head = run(rules, tape, head, 'A', 5)
        ht += 1
        hk += int(steps == 1 and state == 'Z' and sum(1 for s in tape.values() if s) == a + 1 + k + 1)
    lines.append(f'B(k, 0, a) with context 2 halts in one step with a + k + 2 nonblank cells: {hk}/{ht}')
    mk, mt = 0, 0
    for k in (1, 2):
        tape, head = b_config(k, 3, 0, [2])
        want = cost(k, 3, 0) + 1
        steps, state, tape, head = run(rules, tape, head, 'A', want + 10)
        mt += 1
        mk += int(steps == want and state == 'Z' and sum(1 for s in tape.values() if s) == result(k, 3, 0) + k + 2)
    lines.append(f'truncated champions B(1, 3, 0) 2 and B(2, 3, 0) 2 halt at 1 + clock (52 and 1168): {mk}/{mt}')
    return e and ok == tot and hk == ht and mk == mt, lines


# ---------- residues ----------

def md(a, b):
    return 2 ** a * 5 ** b


SMALL = {0: 1, 1: 2, 2: 4, 3: 16}


def small_tow(h):
    return SMALL.get(h, 65536)


@lru_cache(maxsize=None)
def tow_mod(h, a, b):
    """2^^h mod 2^a 5^b (a <= 65536)."""
    if h == 0:
        return 1 % md(a, b)
    hh = h - 1
    if b == 0:
        return pow(2, small_tow(hh), md(a, 0)) if hh < 4 else 0
    if hh < 4:
        return pow(2, small_tow(hh), md(a, b))
    return pow(2, tow_mod(hh, 2, b - 1) + md(2, b - 1) * a, md(a, b))


class Read:
    """tau and sigma mod 10^D."""

    def __init__(self, D):
        self.D, self.M, self.m1 = D, md(D, D), md(2, D - 1)
        self.inv3 = (2 * self.M + 1) // 3
        self.tall = D + 6
        self.S1 = sum(self.term1(i) for i in range(D + 4))
        self.t_inf = self.term1(D + 4)

    def tw0(self, h):
        return tow_mod(h, self.D, self.D)

    def tw1(self, h):
        return tow_mod(h, 2, self.D - 1)

    def T0part(self, h):
        """T_0(2^^h - 2, 0) mod M."""
        M, m1 = self.M, self.m1
        if h <= 3:
            e1, e2 = small_tow(h) - 2, 2 * (small_tow(h) - 2)
        else:
            r = (self.tw1(h) + m1 - 2) % m1
            e1, e2 = r + m1 * self.D, 2 * r % m1 + m1 * self.D
        Nm, P2, P4 = (self.tw0(h) + M - 2) % M, pow(2, e1, M), pow(2, e2, M)
        return self.inv3 * (64 * P4 + 8 + 81 * M - (72 * P2 + 9 * Nm)) % M

    def term1(self, i):
        return (C2((self.tw0(i + 2) + self.M - 4) % self.M, 0) + self.T0part(i + 2)) % self.M

    def Nres(self, h):
        return (self.tw0(h) + self.M - 2) % self.M

    def u(self, k, ht, v):
        return (C2((self.tw0(ht) + self.M - 4) % self.M, k) + v) % self.M

    def L(self, k, h):
        """T_k(2^^h - 2, 0) mod M for h = 2, 3 (k <= 1), 4, tall."""
        M = self.M
        if k == 0:
            return self.T0part(h)
        if k == 1:
            if h <= 3:
                return sum(self.term1(i) for i in range(small_tow(h) - 2)) % M
            return (self.S1 + (self.Nres(h) + M - (self.D + 4)) % M * self.t_inf) % M
        p2, p4, pt = self.V(k - 1)
        if k == 2:
            return (self.u(1, 2, p2) + self.u(1, 4, p4) + (self.Nres(h) + M - 2) % M * self.u(1, self.tall, pt)) % M
        return (self.u(k - 1, 2, p2) + (self.Nres(h) + M - 1) % M * self.u(k - 1, self.tall, pt)) % M

    @lru_cache(maxsize=None)
    def V(self, k):
        return (self.L(k, 2), self.L(k, 4), self.L(k, self.tall))

    def tau(self):
        p2, _, pt = self.V(13)
        return (241 + self.u(13, 2, p2) + 2 * self.u(13, self.tall, pt) + 1) % self.M

    def sigma(self):
        return (self.tw0(self.tall) + self.M - 4 + 18) % self.M


def check_residues():
    """The residue read against stored integers, and against itself across moduli."""
    lines, good = [], True
    r = Read(40)
    exact = [(0, 2, T(0, 2, 0)), (0, 3, T(0, 14, 0)), (1, 2, T(1, 2, 0))]
    e = all(r.L(k, h) == v % r.M for k, h, v in exact)
    lines.append(f'T_0(2, 0), T_0(14, 0), T_1(2, 0) mod 10^40 equal the stored integers: {e}')
    good &= e
    big = T(0, 65534, 0)
    e = r.L(0, 4) == big % r.M
    lines.append(f'T_0(65534, 0) (a {big.bit_length()}-bit integer) mod 10^40 equals the read: {e}')
    good &= e
    return good, lines


def main():
    digits = int(sys.argv[sys.argv.index('--digits') + 1]) if '--digits' in sys.argv else 200
    rows = sys.argv[sys.argv.index('--rows') + 1] if '--rows' in sys.argv else ROWS
    print(f'machine {rows}')
    ok1, lines = check_machine(parse(rows))
    for line in lines:
        print('  ' + line)
    ok2, lines = check_residues()
    for line in lines:
        print('  ' + line)
    full = Read(digits)
    tau, sigma = full.tau(), full.sigma()
    ok3 = True
    for d in sorted({10, digits // 4, digits // 2}):
        if 6 <= d < digits:
            part = Read(d)
            c = part.tau() == tau % 10 ** d and part.sigma() == sigma % 10 ** d
            print(f'  the read at 10^{d} equals the read at 10^{digits} reduced: {c}')
            ok3 &= c
    print(f'tau mod 10^{digits}:')
    print('  ' + str(tau).zfill(digits))
    print(f'sigma mod 10^{digits}:')
    print('  ' + str(sigma).zfill(digits))
    if not (ok1 and ok2 and ok3):
        print('A CHECK FAILED')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
