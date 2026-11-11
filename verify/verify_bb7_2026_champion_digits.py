"""Standalone verifier: the last D decimal digits of the step count and score of the BB(7) machine of October 2026.

Machine 1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB (Ketchersid, October 2026). Python standard library only.
The fourteen rows are an argument (--rows); every rule below is checked on the machine built from them.

Configuration K(a; d_1 .. d_n) = 0^inf E> 0 1 00 (11)^a 00 (11)^d_1 00 .. (11)^d_n 00 1 0^inf (Ketchersid's form).
    D   : K(a; d+1, R)        -> K(3a+3; d, R)                     in 12a^2 + 66a + 58 steps
    B_k : K(a; 0^k, y+1, R)   -> K(1; 1^(k-1), 3a+3-k, y, R)       in 12a^2 + 18a + 8(k+2)(3a-k) + 4k^2 + 40k + 58,  1 <= k <= 3a
    E   : K(a; 0^20)          -> halt, 6a + 7 ones                 in 48a^2 + 198a - 456 steps, the halting row counted
    blank tape -> K(8; 0, 1^19) at step 3959
Maps and clock (from D and B_k by induction on the position k, then on the count n):
    V_0(x) = 3x + 3,  s_0 = 1,  s_(k+1) = V_k(s_k),  V_(k+1)(x) = V_k^(3x+2-k)(s_k)
    K(a; 0^k, n, R) -> K(V_k^n(a); 0^k, 0, R) in T_k(n, a) steps;   K(1; 1^k, R) -> K(s_k; 0^k, R) in P_k steps
    T_0(n, a) = sum_(i<n) [12 x_i^2 + 66 x_i + 58],  x_i = V_0^i(a)
    T_(k+1)(n, a) = sum_(i<n) [cB(x_i, k+1) + P_k + T_k(3 x_i + 2 - k, s_k)],  x_i = V_(k+1)^i(a),  P_(k+1) = P_k + T_k(1, s_k)
    Acc_0 = 8,  Acc_(i+1) = V_(i+1)(Acc_i);   tau = 3959 + sum_(i<19) T_(i+1)(1, Acc_i) + [48 Acc_19^2 + 198 Acc_19 - 456]
    sigma = 6 Acc_19 + 7

Residues mod M = 10^D, with Q(b) = 4 10^b:
    2 V_1(x) + 3 = 5 3^(3x+2), and 3^(Q(b)) = 1 mod 2 Q(b+1): V_1(x) mod Q(b+1) is a function of x mod Q(b).
    V_1 flips parity; a V_1-iterate of height above b has its residue mod Q(b) fixed by its parity.
    8 T_0(n, 1) = 75 9^n + 300 3^n - 112 n - 375, so T_0(3x+2, 1) mod M is read from x and V_1(x) mod 400 M.
    T_1(N, 6) = sum of the level-1 summand along V_1^i(6): D + 4 first summands, then two alternating ones.
    For k >= 2 every V_k-iterate in play is such a V_1-iterate, so each level is two alternating summands, counted.

    python3 verify_bb7_2026_champion_digits.py [--digits 200] [--rows 1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB]
"""
import sys

ROWS = '1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB'
ENTRY = 3959
S2 = 8716961001
A1 = 6354664570821


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


def k_config(a, ds):
    """K(a; ds): the set of ones with the head (state E) at cell 0."""
    cells = [0, 1, 0, 0] + [1] * (2 * a) + [0, 0]
    for d in ds:
        cells += [1] * (2 * d) + [0, 0]
    cells += [1]
    return {i for i, c in enumerate(cells) if c}


def lands(rules, a, ds, steps, a2, ds2):
    n, state, ones, head = run(rules, k_config(a, ds), 0, 'E', steps)
    return n == steps and state == 'E' and {i - head for i in ones} == k_config(a2, ds2)


def cD(a):
    return 12 * a * a + 66 * a + 58


def cB(a, k):
    return 12 * a * a + 18 * a + 8 * (k + 2) * (3 * a - k) + 4 * k * k + 40 * k + 58


def V(k, x):
    if k == 0:
        return 3 * x + 3
    y = s(k - 1)
    for _ in range(3 * x + 2 - (k - 1)):
        y = V(k - 1, y)
    return y


def s(k):
    return 1 if k == 0 else V(k - 1, s(k - 1))


def P(k):
    return 0 if k == 0 else P(k - 1) + T(k - 1, 1, s(k - 1))


def T(k, n, a):
    total = 0
    for i in range(n):
        total += cD(a) if k == 0 else cB(a, k) + P(k - 1) + T(k - 1, 3 * a + 2 - (k - 1), s(k - 1))
        if i < n - 1:
            a = V(k, a)
    return total


def check_machine(rules):
    lines = []
    n, state, ones, head = run(rules, set(), 0, 'A', ENTRY)
    e = n == ENTRY and state == 'E' and {i - head for i in ones} == k_config(8, [0] + [1] * 19)
    lines.append(f'blank tape at step {ENTRY} is K(8; 0, 1^19): {e}')
    ok = tot = 0
    for a in range(0, 7):
        for d in range(0, 3):
            for rest in ([], [2], [0, 1]):
                tot += 1
                ok += int(lands(rules, a, [d + 1] + rest, cD(a), 3 * a + 3, [d] + rest))
    lines.append(f'rule D at exactly 12a^2 + 66a + 58 steps: {ok}/{tot}')
    okb = totb = 0
    for k in range(1, 20):
        for a in range((k + 2) // 3, (k + 2) // 3 + 3):
            for y in (0, 2):
                for rest in ([], [1]):
                    totb += 1
                    okb += int(lands(rules, a, [0] * k + [y + 1] + rest, cB(a, k), 1,
                                     [1] * (k - 1) + [3 * a + 3 - k, y] + rest))
    lines.append(f'rule B_k, k = 1..19, at exactly its step count: {okb}/{totb}')
    oke = tote = 0
    for a in range(7, 13):
        want = 48 * a * a + 198 * a - 456
        n, state, ones, head = run(rules, k_config(a, [0] * 20), 0, 'E', want + 5)
        tote += 1
        oke += int(n == want and state == 'Z' and len(ones) == 6 * a + 7)
    lines.append(f'rule E: K(a; 0^20) halts at exactly 48a^2 + 198a - 456 with 6a + 7 ones: {oke}/{tote}')
    okh = toth = 0
    for k, n_, a in ((0, 1, 2), (0, 3, 1), (0, 4, 0), (1, 1, 1)):
        res = a
        for _ in range(n_):
            res = V(k, res)
        for rest in ([], [1, 0]):
            toth += 1
            okh += int(lands(rules, a, [0] * k + [n_] + rest, T(k, n_, a), res, [0] * (k + 1) + rest))
    okh += int(lands(rules, 1, [1, 2], P(1), s(1), [0, 2]))
    toth += 1
    lines.append(f'the clock T_k(n, a) and P_1 on the machine, to {T(1, 1, 1)} steps: {okh}/{toth}')
    return e and ok == tot and okb == totb and oke == tote and okh == toth, lines


# ---------- residues ----------

def T0x(n):
    return (75 * 9 ** n + 300 * 3 ** n - 112 * n - 375) // 8


class Read:
    """tau and sigma mod 10^D."""

    def __init__(self, D):
        self.Mn, self.B, self.i0 = 10 ** D, D + 2, D + 4
        self.Q2 = self.Q(self.B)
        fs = [self.f1(i) for i in range(self.i0 + 2)]
        self.c = (self.Om(0), self.Om(1), sum(fs[:self.i0]) % self.Mn, fs[self.i0], fs[self.i0 + 1])
        self.period = fs[self.i0] == self.f1(self.i0 + 2) and fs[self.i0 + 1] == self.f1(self.i0 + 3)

    @staticmethod
    def Q(b):
        return 4 * 10 ** b

    def v1step(self, r, b):
        m2 = 2 * self.Q(b + 1)
        return ((5 * pow(3, 3 * r + 2, m2) + m2 - 3) % m2) // 2

    def R(self, i, b):
        """V_1^i(6) mod Q(b)."""
        j = i - b
        if j >= 0:
            r, start = (2 if j % 2 == 0 else 1), 0
        else:
            r, start = 6, -j
        for level in range(start, b):
            r = self.v1step(r, level)
        return r

    def Om(self, p):
        return self.R(2 * self.B + 2 + p % 2, self.B)

    def T0R(self, rx, rv):
        m = 200 * self.Mn
        return ((75 * (2 * rv + 3) ** 2 + 1500 * (2 * rv + 3) + 20000 * m - (9375 + 2800 * (3 * rx + 2))) % m) // 200

    def cBr(self, r, k):
        Mn = self.Mn
        return (12 * r * r + (24 * k + 66) * r + (4 * k * k + 40 * k + 58) + Mn - 8 * (k + 2) * k) % Mn

    def f1(self, i):
        r = self.R(i, self.B)
        return (self.cBr(r % self.Mn, 1) + self.T0R(r, self.v1step(r, self.B) % self.Q2)) % self.Mn

    def hm(self, y):
        return (y % (2 * self.Mn)) // 2

    def xs(self, p):
        return self.c[p % 2]

    def L1(self, n2):
        Mn, c = self.Mn, self.c
        return (c[2] + self.hm(n2 + 2 * Mn - (self.i0 - 1)) * c[3] + self.hm(n2 + 2 * Mn - self.i0) * c[4]) % Mn

    def nS(self, k, p):
        Mn = self.Mn
        return (3 * (self.xs(p) % (2 * Mn)) + 2 + 2 * Mn - k) % (2 * Mn)

    def term2x(self, x):
        Mn = self.Mn
        return (self.cBr(x % Mn, 2) + 136 + self.L1((3 * x + 1) % (2 * Mn))) % Mn

    def tNext(self, q, k, p):
        return (self.cBr(self.xs(p) % self.Mn, k + 1) + q[4] + q[2 + p % 2]) % self.Mn

    def step(self, q, k):
        Mn, hm, nS, tN = self.Mn, self.hm, self.nS, self.tNext
        add = 136 if k == 0 else 1050 + T0x(20) if k == 1 else self.term2x(S2) if k == 2 else q[(k + 1) % 2]

        def lNext(p):
            if k == 0:
                return self.L1(nS(1, p))
            if k == 1:
                return (self.term2x(S2) + tN(q, 1, 0) + hm(nS(2, p) + 2 * Mn - 1) * tN(q, 1, 1)
                        + hm(nS(2, p) + 2 * Mn - 2) * tN(q, 1, 0)) % Mn
            return (hm(nS(k + 1, p) + 1) * tN(q, k, k) + hm(nS(k + 1, p)) * tN(q, k, k + 1)) % Mn
        return (tN(q, k, 0), tN(q, k, 1), lNext(0), lNext(1), (q[4] + add) % Mn)

    def levels(self):
        c = self.c
        q = (0, 0, self.T0R(c[0], c[1]), self.T0R(c[1], c[0]), 0)
        out = [q]
        for k in range(19):
            q = self.step(q, k)
            out.append(q)
        return out

    def tau(self):
        Mn, st = self.Mn, self.levels()
        r = self.c[1] % Mn
        top = sum(st[j + 3][j % 2] for j in range(17))
        return (ENTRY + (1566 + T0x(26)) + self.term2x(A1) + top + (48 * r * r + 198 * r + Mn - 456) % Mn) % Mn

    def sigma(self):
        return (6 * (self.c[1] % self.Mn) + 7) % self.Mn


def check_residues():
    lines, good = [], True
    r = Read(30)
    e = all(r.T0R(x % r.Q2, V(1, x) % r.Q2) == T(0, 3 * x + 2, 1) % r.Mn for x in range(1, 5))
    lines.append(f'T_0(3x + 2, 1) mod 10^30 from x and V_1(x) mod 4 10^32 equals the stored integer, x = 1..4: {e}')
    good &= e
    e = r.f1(0) == (cB(6, 1) + T(0, 20, 1)) % r.Mn and V(1, 6) == S2 and V(1, 8) == A1
    lines.append(f'the level-1 summand at 6 equals the stored integer; V_1(6) and V_1(8) are the two constants: {e}')
    good &= e
    e = all(r.R(i, 6) == (6 if i == 0 else V(1, 6) if i == 1 else None) % r.Q(6) for i in (0, 1))
    lines.append(f'V_1^i(6) mod 4 10^6 by the residue chain equals the stored integer, i = 0, 1: {e}')
    good &= e
    lines.append(f'the level-1 summand has period 2 from index D + 4 (checked at D = 30): {r.period}')
    return good and r.period, lines


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
    ok3 = full.period
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
