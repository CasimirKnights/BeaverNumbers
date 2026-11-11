"""Standalone verifier: the last D decimal digits of the step count and score of the BB(7) champion that preceded the
machine of October 2026.

Machine 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF. Python standard library only. The fourteen rows are an
argument (--rows); every rule below is checked on the machine built from them.

Configuration B(a; b, c, .., z) = 0^inf 111 (01)^(3z+1) 1 .. (01)^(3c+1) 1 (01)^(3b+1) 1 1 (01)^(3a+1) 0011100 A> 0^inf.
    B(a; b+1, R)             -> B(2a+4; b, R)            in C1(a) = 36a^2 + 318a + 590 steps
    B(a; 0^k, 0, n+1, R)     -> B(0; 0^k, a+2, n, R)     in C2(a, k) = (24 + 8k)(3a + 1) + 226 + 48k steps
    B(a; 0^k)                -> halt, 3a + 2k + 10 ones  in CH(a, k) = (2 + 8k)(3a + 1) + 27 + 21k steps
    blank tape -> B(4; 1^12) at step 8574 (the first configuration with twelve 1-blocks)
Clock, g_0(x) = 2x + 4, g_(k+1)(x) = g_k^(x+2)(0), g_k(x) = 2^(k)(x + 4) - 4 (Knuth arrows, 2^(0) y = 2y):
    B(a; 0^k, n, R) -> B(g_k^n(a); 0^k, 0, R) in T_k(n, a) steps
    T_0(n, a) = sum_(i<n) C1(a_i),  a_(i+1) = g_0(a_i)
    T_(k+1)(n, a) = sum_(i<n) [C2(a_i, k) + T_k(a_i + 2, 0)],  a_(i+1) = g_(k+1)(a_i)
    A_0 = 4,  A_(j+1) = g_j(A_j);   tau = 8574 + sum_(j<12) T_j(1, A_j) + CH(A_12, 12),   sigma = 3 A_12 + 34

Residues mod M = 10^D. With N = 2^^h - 2:  3 T_0(N, 0) + 936 + 318 N = 576 4^N + 360 2^N, read with the inverse of 3
and 2^N, 4^N by exponent reduction (2^x mod 2^a 5^(b+1) depends on x mod 4 5^b for x >= a); 2^^h mod 2^a 5^b is one
constant for h >= b + 6.  T_1(N, 0) is its first D + 4 summands and one repeating summand; T_(k+1)(N, 0) is one or two
first summands and one repeating summand of level k.  A_1 + 4 = 2^^3, A_2 + 4 = 2^^4, A_j + 4 a tall tower for j >= 3.

    python3 verify_bb7_champion_digits.py [--digits 200] [--rows 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF]
"""
import sys
from functools import lru_cache

sys.setrecursionlimit(100000)
ROWS = '1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF'
ENTRY = 8574


# ---------- the machine ----------

def parse(rows):
    out = {}
    for q, block in zip('ABCDEFG', rows.split('_')):
        for bit in (0, 1):
            w, d, t = block[3 * bit:3 * bit + 3]
            out[(q, bit)] = (int(w), 1 if d == 'R' else -1, t)
    return out


def run(rules, ones, head, state, steps):
    """`steps` steps (fewer if the machine halts); returns (steps taken, state, ones, head)."""
    ones = set(ones)
    for t in range(steps):
        w, d, nxt = rules[(state, int(head in ones))]
        (ones.add if w else ones.discard)(head)
        head += d
        if nxt == 'Z':
            return t + 1, 'Z', ones, head
        state = nxt
    return steps, state, ones, head


def b_config(a, blocks):
    """B(a; blocks): (ones, head), state A on the blank cell right of the word."""
    word = '111'
    for x in reversed(blocks):
        word += '01' * (3 * x + 1) + '1'
    word += '1' + '01' * (3 * a + 1) + '0011100'
    return {i for i, ch in enumerate(word) if ch == '1'}, len(word)


def lands(rules, a, blocks, steps, a2, blocks2):
    ones, head = b_config(a, blocks)
    n, state, ones, head = run(rules, ones, head, 'A', steps)
    want, wh = b_config(a2, blocks2)
    return n == steps and state == 'A' and {i - head for i in ones} == {i - wh for i in want}


def C1(a):
    return 36 * a * a + 318 * a + 590


def C2(a, k):
    return (24 + 8 * k) * (3 * a + 1) + 226 + 48 * k


def CH(a, k):
    return (2 + 8 * k) * (3 * a + 1) + 27 + 21 * k


def g(k, x):
    if k == 0:
        return 2 * x + 4
    y = 0
    for _ in range(x + 2):
        y = g(k - 1, y)
    return y


def T(k, n, a):
    total = 0
    for i in range(n):
        total += C1(a) if k == 0 else C2(a, k - 1) + T(k - 1, a + 2, 0)
        if i < n - 1:
            a = g(k, a)
    return total


def check_machine(rules):
    lines = []
    n, state, ones, head = run(rules, set(), 0, 'A', ENTRY)
    want, wh = b_config(4, [1] * 12)
    e = n == ENTRY and state == 'A' and {i - head for i in ones} == {i - wh for i in want}
    lines.append(f'blank tape at step {ENTRY} is B(4; 1^12): {e}')
    ok = tot = 0
    for a in range(0, 5):
        for b in range(0, 3):
            for rest in ([], [2], [0, 1]):
                tot += 1
                ok += int(lands(rules, a, [b + 1] + rest, C1(a), 2 * a + 4, [b] + rest))
    lines.append(f'B(a; b+1, R) -> B(2a+4; b, R) at exactly C1(a) steps: {ok}/{tot}')
    ok2 = tot2 = 0
    for k in range(0, 5):
        for a in range(0, 4):
            for m in (0, 2):
                for rest in ([], [1]):
                    tot2 += 1
                    ok2 += int(lands(rules, a, [0] * k + [0, m + 1] + rest, C2(a, k), 0, [0] * k + [a + 2, m] + rest))
    lines.append(f'B(a; 0^k, 0, n+1, R) -> B(0; 0^k, a+2, n, R) at exactly C2(a, k) steps: {ok2}/{tot2}')
    okh = toth = 0
    for k in range(0, 5):
        for a in range(0, 4):
            ones, head = b_config(a, [0] * k)
            n, state, ones, head = run(rules, ones, head, 'A', CH(a, k) + 5)
            toth += 1
            okh += int(n == CH(a, k) and state == 'Z' and len(ones) == 3 * a + 2 * k + 10)
    lines.append(f'B(a; 0^k) halts at exactly CH(a, k) steps with 3a + 2k + 10 ones: {okh}/{toth}')
    okc = totc = 0
    for k, n_, a in ((0, 1, 3), (0, 2, 0), (0, 3, 1), (1, 1, 0), (1, 1, 1), (1, 2, 0)):
        res = a
        for _ in range(n_):
            res = g(k, res)
        for rest in ([], [1, 0]):
            if T(k, n_, a) > 3_000_000:
                continue
            totc += 1
            okc += int(lands(rules, a, [0] * k + [n_] + rest, T(k, n_, a), res, [0] * (k + 1) + rest))
    lines.append(f'the clock T_k(n, a) on the machine: {okc}/{totc}')
    return e and ok == tot and ok2 == tot2 and okh == toth and okc == totc, lines


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
        return self.inv3 * (576 * P4 + 360 * P2 + 319 * M - (936 + 318 * Nm)) % M

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

    def Ares(self):
        return (self.tw0(self.tall) + self.M - 4) % self.M

    def tau(self):
        A = self.Ares()
        total = ENTRY + C1(4) + (C2(12, 0) + self.T0part(3)) + (C2(65532, 1) + self.V(1)[1])
        total += sum(C2(A, j) + self.V(j)[2] for j in range(2, 11)) + CH(A, 12)
        return total % self.M

    def sigma(self):
        return (3 * self.Ares() + 34) % self.M


def check_residues():
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
    e = g(0, 4) == 12 and g(1, 12) == 65532
    lines.append(f'A_1 = 12 and A_2 = 65532: {e}')
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
