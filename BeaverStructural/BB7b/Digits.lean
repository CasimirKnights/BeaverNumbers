import BeaverStructural.BB7b.Residues

/-! The step count τ and the score σ of the BB(7) machine of October 2026 mod Mn = 10^200.
Q 202 = 400·Mn.  A V_1-iterate x of height 204 (`Stab x`) has x mod Q 202 = `xr (x % 2)` (`stab_res`).
Level 0: T_0(3x + 2, 1) mod Mn = `T0R (x mod Q 202) (V_1(x) mod Q 202)` (`T0_res`).
Level 1: the summand at V_1^i(6) is `f1 i` mod Mn (`f1_eq`), of period 2 from i = 204, so T_1(N, 6) mod Mn is
`L1` of N mod 2·Mn: the first 204 summands and two counts (`L1_eq`).
Levels k ≥ 2: `st par0 k` holds P_k, T_k(3x + 2 − k, s_k) and T_k(1, x) mod Mn for stable x of each parity
(`Inv`, `st_ok`); each level is the previous one's two alternating summands counted (`sum_alt`, `sum_alt0`).
τ mod Mn = `tauModP par0` (`tau_mod`), σ mod Mn = `sigmaModP par0` (`sigma_mod`). -/

namespace BeaverStructural.BB7b

open Finset
open BeaverStructural.BB7 (md powMod sumF sumF_eq sumF_mod sub_mod')

/-- Mn = 10^200. -/
def Mn : ℕ := md 200 200

theorem Mn_eq : Mn = 10 ^ 200 := by decide +kernel

theorem Mn_big : 100000 ≤ Mn := by unfold Mn md; norm_num

theorem Q2_eq : Q 202 = 400 * Mn := by decide +kernel

theorem Mn_dvd_Q : Mn ∣ Q 202 := ⟨400, by rw [Q2_eq]; ring⟩

theorem two_Mn_dvd_Q : 2 * Mn ∣ Q 202 := ⟨200, by rw [Q2_eq]; ring⟩

theorem c200_Mn_dvd_Q : 200 * Mn ∣ Q 202 := ⟨2, by rw [Q2_eq]; ring⟩

theorem Q_dvd_succ (b : ℕ) : Q b ∣ Q (b + 1) := ⟨10, by rw [Q_succ]; ring⟩

theorem modeq_of_mod {a b : ℕ} (h : a % Mn = b) : a ≡ b [MOD Mn] := by
  subst h; exact (Nat.mod_modEq a Mn).symm

/-- X mod m from X + c ≡ E. -/
theorem modEq_sub_of {X E c m : ℕ} (hc : c ≤ m) (h : X + c ≡ E [MOD m]) : X % m = (E + m - c) % m := by
  show X ≡ E + m - c [MOD m]
  apply Nat.ModEq.add_right_cancel' c
  rw [Nat.sub_add_cancel (by omega)]
  exact h.trans (by show E % m = (E + m) % m; rw [Nat.add_mod_right])

theorem add3_mod (a b c m : ℕ) : (a + b + c) % m = (a % m + b % m + c % m) % m :=
  ((Nat.mod_modEq a m).symm.add (Nat.mod_modEq b m).symm).add (Nat.mod_modEq c m).symm

theorem sumF_add (f : ℕ → ℕ) (a b : ℕ) : sumF f (a + b) = sumF f a + sumF (fun i => f (a + i)) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [show a + (b + 1) = (a + b) + 1 by ring, sumF, ih, sumF, Nat.add_assoc]

theorem sumF_mod_lt (f h : ℕ → ℕ) (m : ℕ) :
    ∀ n, (∀ i, i < n → f i % m = h i % m) → sumF f n % m = sumF h n % m := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hf
    exact Nat.ModEq.add (ih (fun i hi => hf i (by omega))) (hf n (by omega))

theorem sumF_shift2 (G : ℕ → ℕ) : ∀ n, sumF G (n + 2) = G 0 + G 1 + sumF (fun j => G (j + 2)) n := by
  intro n
  induction n with
  | zero =>
    show 0 + G 0 + G 1 = G 0 + G 1 + 0
    ring
  | succ n ih =>
    show sumF G (n + 2) + G (n + 2) = G 0 + G 1 + (sumF (fun j => G (j + 2)) n + G (n + 2))
    rw [ih]; ring

/-- A sequence of period 2 from i0 on takes the values g i0, g (i0 + 1) alternately. -/
theorem per_pair (g : ℕ → ℕ) (i0 : ℕ) (hper : ∀ i, i0 ≤ i → g (i + 2) = g i) :
    ∀ j, g (i0 + 2 * j) = g i0 ∧ g (i0 + 2 * j + 1) = g (i0 + 1) := by
  intro j
  induction j with
  | zero => exact ⟨rfl, rfl⟩
  | succ j ih =>
    refine ⟨?_, ?_⟩
    · rw [show i0 + 2 * (j + 1) = (i0 + 2 * j) + 2 by ring, hper _ (by omega)]
      exact ih.1
    · rw [show i0 + 2 * (j + 1) + 1 = (i0 + 2 * j + 1) + 2 by ring, hper _ (by omega)]
      exact ih.2

/-- The sum of a sequence of period 2 from i0 on: the prefix and the two counts. -/
theorem sum_alt (g : ℕ → ℕ) (i0 : ℕ) (hper : ∀ i, i0 ≤ i → g (i + 2) = g i) :
    ∀ n, sumF g (i0 + n) = sumF g i0 + (n + 1) / 2 * g i0 + n / 2 * g (i0 + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show i0 + (n + 1) = (i0 + n) + 1 from (Nat.add_assoc i0 n 1).symm, sumF, ih]
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' n
    · subst hj
      have h1 : (2 * j + 1) / 2 = j := by omega
      have h2 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
      have h3 : 2 * j / 2 = j := by omega
      rw [(per_pair g i0 hper j).1, h1, h2, h3]
      ring
    · subst hj
      have h1 : (2 * j + 1) / 2 = j := by omega
      have h2 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
      have h3 : (2 * j + 1 + 1 + 1) / 2 = j + 1 := by omega
      rw [show i0 + (2 * j + 1) = i0 + 2 * j + 1 from (Nat.add_assoc i0 (2 * j) 1).symm,
        (per_pair g i0 hper j).2, h1, h2, h3]
      ring

theorem sum_alt0 (g : ℕ → ℕ) (hper : ∀ i, g (i + 2) = g i) (n : ℕ) :
    sumF g n = (n + 1) / 2 * g 0 + n / 2 * g 1 := by
  have e := sum_alt g 0 (fun i _ => hper i) n
  rw [Nat.zero_add n, show sumF g 0 = 0 from rfl, Nat.zero_add ((n + 1) / 2 * g 0)] at e
  exact e

/-- T_0(3x + 2, 1) mod Mn from x and V_1(x) mod 200·Mn. -/
def T0R (rx rv : ℕ) : ℕ :=
  (75 * (2 * rv + 3) ^ 2 + 1500 * (2 * rv + 3) + 20000 * (200 * Mn) - (9375 + 2800 * (3 * rx + 2))) %
    (200 * Mn) / 200

theorem T0R_le (rx m B : ℕ) (hrx : rx < 400 * m) (hm : 100000 ≤ m) :
    9375 + 2800 * (3 * rx + 2) ≤ B + 20000 * (200 * m) := by
  have h1 : 8400 * rx ≤ 8400 * (400 * m) := Nat.mul_le_mul_left 8400 hrx.le
  have h2 : 9375 + 2800 * (3 * rx + 2) = 14975 + 8400 * rx := by ring
  have h3 : 20000 * (200 * m) = 640000 * m + 8400 * (400 * m) := by ring
  have h4 : 14975 ≤ 640000 * m := le_trans (by norm_num) (Nat.mul_le_mul_left 640000 hm)
  rw [h2, h3]
  exact le_trans (Nat.add_le_add h4 h1) (Nat.le_add_left _ B)

theorem T0R_spec (t x v rx rv : ℕ)
    (H : 200 * t + (9375 + 2800 * (3 * x + 2)) = 75 * (2 * v + 3) ^ 2 + 1500 * (2 * v + 3))
    (hx : rx ≡ x [MOD 200 * Mn]) (hv : rv ≡ v [MOD 200 * Mn]) (hrx : rx < 400 * Mn) :
    t % Mn = T0R rx rv := by
  have hle : 9375 + 2800 * (3 * rx + 2) ≤
      75 * (2 * rv + 3) ^ 2 + 1500 * (2 * rv + 3) + 20000 * (200 * Mn) := by
    exact T0R_le rx Mn _ hrx Mn_big
  have hA : 75 * (2 * rv + 3) ^ 2 + 1500 * (2 * rv + 3) + 20000 * (200 * Mn) - (9375 + 2800 * (3 * rx + 2))
      ≡ 200 * t [MOD 200 * Mn] := by
    apply Nat.ModEq.add_right_cancel' (9375 + 2800 * (3 * rx + 2))
    rw [Nat.sub_add_cancel hle]
    have h1 : 200 * t + (9375 + 2800 * (3 * rx + 2)) ≡ 200 * t + (9375 + 2800 * (3 * x + 2))
        [MOD 200 * Mn] :=
      Nat.ModEq.add_left _ ((((hx.mul_left 3).add_right 2).mul_left 2800).add_left 9375)
    rw [H] at h1
    have h2 : 75 * (2 * v + 3) ^ 2 + 1500 * (2 * v + 3) ≡ 75 * (2 * rv + 3) ^ 2 + 1500 * (2 * rv + 3)
        [MOD 200 * Mn] :=
      ((((hv.symm.mul_left 2).add_right 3).pow 2).mul_left 75).add
        (((hv.symm.mul_left 2).add_right 3).mul_left 1500)
    have h3 : 75 * (2 * rv + 3) ^ 2 + 1500 * (2 * rv + 3) ≡
        75 * (2 * rv + 3) ^ 2 + 1500 * (2 * rv + 3) + 20000 * (200 * Mn) [MOD 200 * Mn] := by
      show _ % (200 * Mn) = _ % (200 * Mn)
      rw [Nat.add_mul_mod_self_right]
    exact (h1.trans (h2.trans h3)).symm
  have hA' : (75 * (2 * rv + 3) ^ 2 + 1500 * (2 * rv + 3) + 20000 * (200 * Mn) -
      (9375 + 2800 * (3 * rx + 2))) % (200 * Mn) = 200 * t % (200 * Mn) := hA
  unfold T0R
  rw [hA', Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ (by norm_num)]

theorem nine_pow (n : ℕ) : (9 : ℕ) ^ n = (3 ^ n) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

theorem T0_res (x : ℕ) : T 0 (3 * x + 2) 1 % Mn = T0R (x % Q 202) (V 1 x % Q 202) := by
  have H : 200 * T 0 (3 * x + 2) 1 + (9375 + 2800 * (3 * x + 2)) =
      75 * (2 * V 1 x + 3) ^ 2 + 1500 * (2 * V 1 x + 3) := by
    have h := T0_closed (3 * x + 2)
    rw [nine_pow] at h
    rw [V1_form x]
    generalize T 0 (3 * x + 2) 1 = t at h ⊢
    generalize (3 : ℕ) ^ (3 * x + 2) = Y at h ⊢
    zify at h ⊢
    linear_combination 25 * h
  have hlt : x % Q 202 < 400 * Mn := by
    rw [← Q2_eq]
    exact Nat.mod_lt _ (by have := Q_ge 202; omega)
  exact T0R_spec _ x (V 1 x) _ _ H (Nat.ModEq.of_dvd c200_Mn_dvd_Q (Nat.mod_modEq x (Q 202)))
    (Nat.ModEq.of_dvd c200_Mn_dvd_Q (Nat.mod_modEq (V 1 x) (Q 202))) hlt

/-- cB(a, k) mod Mn from a mod Mn. -/
def cBr (r k : ℕ) : ℕ :=
  (12 * r * r + (24 * k + 66) * r + (4 * k * k + 40 * k + 58) + Mn - 8 * (k + 2) * k) % Mn

theorem cB_mod (a k : ℕ) (hk : k ≤ 3 * a) (hk20 : k ≤ 20) : cB a k % Mn = cBr (a % Mn) k := by
  have hMb := Mn_big
  have h1 : (k + 2) * k ≤ 22 * 20 := Nat.mul_le_mul (by omega) hk20
  have hle : 8 * (k + 2) * k ≤ Mn := by rw [Nat.mul_assoc]; omega
  have e : cB a k + 8 * (k + 2) * k = 12 * a * a + (24 * k + 66) * a + (4 * k * k + 40 * k + 58) := by
    obtain ⟨n, hn⟩ : ∃ n, 3 * a = n + k := ⟨3 * a - k, by omega⟩
    unfold cB costB
    rw [show 3 * a - k = n by omega]
    zify at hn ⊢
    linear_combination (-8 * ((k : ℤ) + 2)) * hn
  have h : a ≡ a % Mn [MOD Mn] := (Nat.mod_modEq a Mn).symm
  unfold cBr
  refine modEq_sub_of hle ?_
  rw [e]
  exact (((h.mul_left 12).mul h).add (h.mul_left (24 * k + 66))).add_right _

/-- The residue mod Q 202 of a stable iterate of parity p. -/
def xr (p : ℕ) : ℕ := Om 202 p

theorem xr_mod (p : ℕ) : xr (p % 2) = xr p := by unfold xr Om; rw [Nat.mod_mod]

theorem stab_ge {x : ℕ} (hx : Stab x) : 204 ≤ x := by
  obtain ⟨w, rfl⟩ := hx
  have h := iter_ge (V 1) (V_ge 1) D w
  have hD : D = 204 := D_def
  omega

theorem stab_res {x : ℕ} (hx : Stab x) : x % Q 202 = xr (x % 2) :=
  stab_mod hx 202 (by have hD : D = 204 := D_def; omega)

theorem V1_res (x : ℕ) : V 1 x % Q 202 = v1step (x % Q 202) 202 % Q 202 := by
  rw [← v1_mod x 202, Nat.mod_mod_of_dvd _ (Q_dvd_succ 202)]

theorem stab_T0 {x : ℕ} (hx : Stab x) :
    T 0 (3 * x + 2) 1 % Mn = T0R (xr (x % 2)) (xr ((x + 1) % 2)) := by
  rw [T0_res, stab_res hx, stab_res (stab_V1 hx), V1_parity]

/-- The level-(k + 1) summand at accumulator x. -/
def sterm (k x : ℕ) : ℕ := cB x (k + 1) + P k + T k (3 * x + 2 - k) (s k)

theorem T_succ_eq (k n a : ℕ) : T (k + 1) n a = sumF (fun i => sterm k ((V (k + 1))^[i] a)) n := by
  rw [sumF_eq]; rfl

theorem T_succ_one (k a : ℕ) : T (k + 1) 1 a = sterm k a := by
  rw [T_succ_eq]
  show 0 + sterm k a = sterm k a
  rw [Nat.zero_add]

theorem sterm0_eq (x : ℕ) : sterm 0 x = cB x 1 + T 0 (3 * x + 2) 1 := by
  simp only [sterm, P_zero, s_zero, Nat.sub_zero, Nat.add_zero, Nat.zero_add]

/-- The level-1 summand mod Mn from x mod Q 202. -/
def f1r (r : ℕ) : ℕ := (cBr (r % Mn) 1 + T0R r (v1step r 202 % Q 202)) % Mn

/-- The level-1 summand at V_1^i(6), mod Mn. -/
def f1 (i : ℕ) : ℕ := f1r (R i 202)

theorem sterm0_res (x : ℕ) (hx : 1 ≤ x) : sterm 0 x % Mn = f1r (x % Q 202) := by
  unfold f1r
  rw [sterm0_eq, Nat.add_mod (cB x 1), cB_mod x 1 (by omega) (by norm_num), T0_res, V1_res,
    Nat.mod_mod_of_dvd _ Mn_dvd_Q]

theorem f1_mod (i : ℕ) : f1 i % Mn = f1 i := by unfold f1 f1r; rw [Nat.mod_mod]

theorem f1_period (i : ℕ) (hi : 202 ≤ i) : f1 (i + 2) = f1 i := by
  unfold f1; rw [R_period 202 i hi]

theorem f1_eq (i : ℕ) : sterm 0 ((V 1)^[i] 6) % Mn = f1 i := by
  have h := iter_ge (V 1) (V_ge 1) i 6
  unfold f1
  rw [sterm0_res _ (by omega), R_eq 202 i]

theorem T1_six (N : ℕ) : T 1 N 6 % Mn = sumF f1 N % Mn := by
  have e : T 1 N 6 = sumF (fun i => sterm 0 ((V 1)^[i] 6)) N := T_succ_eq 0 N 6
  rw [e]
  exact sumF_mod _ f1 Mn (fun i => by
    show sterm 0 ((V 1)^[i] 6) % Mn = f1 i % Mn
    rw [f1_eq, f1_mod]) N

/-- The first 204 level-1 summands, mod Mn. -/
def prefF (n : ℕ) : ℕ := sumF f1 n % Mn

def pref1 : ℕ := prefF 204

theorem pref1_eq : pref1 = prefF 204 := rfl

theorem prefF_eq (n : ℕ) : prefF n = sumF f1 n % Mn := rfl

/-- y / 2 mod Mn from y mod 2·Mn. -/
def hm (y : ℕ) : ℕ := y % (2 * Mn) / 2

theorem hm_sub (N c : ℕ) (hc : c ≤ N) (hcM : c ≤ 2 * Mn) :
    hm (N % (2 * Mn) + 2 * Mn - c) = (N - c) / 2 % Mn := by
  unfold hm
  rw [← sub_mod' N c (2 * Mn) hc hcM]
  exact Nat.mod_mul_right_div_self (N - c) 2 Mn

theorem hm_add (N c : ℕ) : hm (N % (2 * Mn) + c) = (N + c) / 2 % Mn := by
  unfold hm
  rw [Nat.mod_add_mod]
  exact Nat.mod_mul_right_div_self (N + c) 2 Mn

theorem hm_self (N : ℕ) : hm (N % (2 * Mn)) = N / 2 % Mn := by
  unfold hm
  rw [Nat.mod_mod]
  exact Nat.mod_mul_right_div_self N 2 Mn

/-- The five numbers of the read: the two stable residues, the level-1 prefix and its two repeating terms. -/
abbrev P5 := ℕ × ℕ × ℕ × ℕ × ℕ

def par0 : P5 := (xr 0, xr 1, pref1, f1 204, f1 205)

theorem par0_x1 : par0.2.1 = xr 1 := by unfold par0; rfl

theorem par0_pf : par0.2.2.1 = pref1 := by unfold par0; rfl

theorem par0_fe : par0.2.2.2.1 = f1 204 := by unfold par0; rfl

theorem par0_fo : par0.2.2.2.2 = f1 205 := by unfold par0; rfl

def xs (c : P5) (p : ℕ) : ℕ := if p % 2 = 0 then c.1 else c.2.1

theorem xs_par0 (p : ℕ) : xs par0 p = xr p := by
  rcases Nat.mod_two_eq_zero_or_one p with h | h
  · rw [← xr_mod p, h]
    show (if p % 2 = 0 then xr 0 else xr 1) = xr 0
    rw [if_pos h]
  · rw [← xr_mod p, h]
    show (if p % 2 = 0 then xr 0 else xr 1) = xr 1
    rw [if_neg (by omega)]

/-- T_1(N, 6) mod Mn from N mod 2·Mn, N ≥ 204. -/
def L1 (c : P5) (n2 : ℕ) : ℕ :=
  (c.2.2.1 + hm (n2 + 2 * Mn - 203) * c.2.2.2.1 + hm (n2 + 2 * Mn - 204) * c.2.2.2.2) % Mn

theorem L1_eq (N : ℕ) (hN : 204 ≤ N) : T 1 N 6 % Mn = L1 par0 (N % (2 * Mn)) := by
  have hMb := Mn_big
  obtain ⟨n, rfl⟩ : ∃ n, N = 204 + n := ⟨N - 204, by omega⟩
  have e := sum_alt f1 204 (fun i hi => f1_period i (by omega)) n
  rw [show (204 : ℕ) + 1 = 205 from rfl] at e
  have h1 : (n + 1) / 2 % Mn = hm ((204 + n) % (2 * Mn) + 2 * Mn - 203) := by
    rw [hm_sub (204 + n) 203 (by omega) (by omega), show 204 + n - 203 = n + 1 by omega]
  have h2 : n / 2 % Mn = hm ((204 + n) % (2 * Mn) + 2 * Mn - 204) := by
    rw [hm_sub (204 + n) 204 (by omega) (by omega), show 204 + n - 204 = n by omega]
  rw [T1_six, e]
  unfold L1
  rw [par0_pf, par0_fe, par0_fo, ← h1, ← h2]
  rw [pref1_eq, prefF_eq]
  exact ((Nat.mod_modEq (sumF f1 204) Mn).symm.add
    ((Nat.mod_modEq ((n + 1) / 2) Mn).symm.mul_right (f1 204))).add
    ((Nat.mod_modEq (n / 2) Mn).symm.mul_right (f1 205))

theorem cD_one : cD 1 = 136 := by unfold cD; norm_num

theorem T0_one (a : ℕ) : T 0 1 a = cD a := by
  have h := T_zero_succ 0 a
  rw [T_none, Nat.add_zero] at h
  exact h

theorem P_one : P 1 = 136 := by
  have h := P_succ 0
  rw [P_zero, s_zero, T0_one, cD_one] at h
  exact h

/-- The level-2 summand at accumulator x, mod Mn, 3x + 1 ≥ 204. -/
def term2x (c : P5) (x : ℕ) : ℕ := (cBr (x % Mn) 2 + 136 + L1 c ((3 * x + 1) % (2 * Mn))) % Mn

theorem term2x_mod (c : P5) (x : ℕ) : term2x c x % Mn = term2x c x := by
  unfold term2x; rw [Nat.mod_mod]

theorem sterm1_res (x : ℕ) (hx : 68 ≤ x) : sterm 1 x % Mn = term2x par0 x := by
  have hMb := Mn_big
  have e : sterm 1 x = cB x 2 + 136 + T 1 (3 * x + 1) 6 := by
    show cB x 2 + P 1 + T 1 (3 * x + 2 - 1) (s 1) = cB x 2 + 136 + T 1 (3 * x + 1) 6
    rw [P_one, s_one, show 3 * x + 2 - 1 = 3 * x + 1 by omega]
  unfold term2x
  rw [e, add3_mod (cB x 2) 136 (T 1 (3 * x + 1) 6) Mn, cB_mod x 2 (by omega) (by norm_num),
    L1_eq (3 * x + 1) (by omega), Nat.mod_eq_of_lt (show 136 < Mn by omega)]

/-- (3x + 2 − k) mod 2·Mn for stable x of parity p. -/
def nS (c : P5) (k p : ℕ) : ℕ := (3 * (xs c p % (2 * Mn)) + 2 + 2 * Mn - k) % (2 * Mn)

theorem nS_eq {x : ℕ} (hx : Stab x) (k : ℕ) (hk : k ≤ 20) (hkx : k ≤ 3 * x + 2) :
    nS par0 k (x % 2) = (3 * x + 2 - k) % (2 * Mn) := by
  have hMb := Mn_big
  unfold nS
  rw [xs_par0, ← stab_res hx, Nat.mod_mod_of_dvd _ two_Mn_dvd_Q]
  refine (modEq_sub_of (by omega) ?_).symm
  rw [Nat.sub_add_cancel hkx]
  exact ((Nat.mod_modEq x (2 * Mn)).symm.mul_left 3).add_right 2

/-- A level: (T_k(1, x) for even x, for odd x, T_k(3x + 2 − k, s_k) for even x, for odd x, P_k), mod Mn. -/
def tSel (q : P5) (p : ℕ) : ℕ := if p % 2 = 0 then q.1 else q.2.1

def lSel (q : P5) (p : ℕ) : ℕ := if p % 2 = 0 then q.2.2.1 else q.2.2.2.1

theorem tSel_congr (q : P5) {a b : ℕ} (h : a % 2 = b % 2) : tSel q a = tSel q b := by
  unfold tSel; rw [h]

/-- T_(k+1)(1, x) mod Mn for stable x of parity p. -/
def tNext (c q : P5) (k p : ℕ) : ℕ := (cBr (xs c p % Mn) (k + 1) + q.2.2.2.2 + lSel q p) % Mn

theorem tNext_congr (c q : P5) (k : ℕ) {a b : ℕ} (h : a % 2 = b % 2) : tNext c q k a = tNext c q k b := by
  unfold tNext xs lSel; rw [h]

theorem tNext_mod (c q : P5) (k p : ℕ) : tNext c q k (p % 2) = tNext c q k p :=
  tNext_congr c q k (Nat.mod_mod p 2)

theorem tNext_modMn (c q : P5) (k p : ℕ) : tNext c q k p % Mn = tNext c q k p := by
  unfold tNext; rw [Nat.mod_mod]

/-- P_(k+1) mod Mn. -/
def prNext (c q : P5) (k : ℕ) : ℕ :=
  (q.2.2.2.2 + (if k = 0 then 136 else if k = 1 then 1050 + T0x 20
    else if k = 2 then term2x c 8716961001 else tSel q (k + 1))) % Mn

/-- T_(k+1)(3x + 1 − k, s_(k+1)) mod Mn for stable x of parity p. -/
def lNext (c q : P5) (k p : ℕ) : ℕ :=
  if k = 0 then L1 c (nS c 1 p)
  else if k = 1 then
    (term2x c 8716961001 + tNext c q 1 0 + hm (nS c 2 p + 2 * Mn - 1) * tNext c q 1 1 +
      hm (nS c 2 p + 2 * Mn - 2) * tNext c q 1 0) % Mn
  else (hm (nS c (k + 1) p + 1) * tNext c q k k + hm (nS c (k + 1) p) * tNext c q k (k + 1)) % Mn

def stepq (c q : P5) (k : ℕ) : P5 :=
  (tNext c q k 0, tNext c q k 1, lNext c q k 0, lNext c q k 1, prNext c q k)

def st (c : P5) : ℕ → P5
  | 0 => (0, 0, T0R (xs c 0) (xs c 1), T0R (xs c 1) (xs c 0), 0)
  | k + 1 => stepq c (st c k) k

theorem st_step (c : P5) (j k : ℕ) (h : k + 1 = j) : st c j = stepq c (st c k) k := by subst h; rfl

theorem sel01 (f : ℕ → ℕ) (p : ℕ) : (if p % 2 = 0 then f 0 else f 1) = f (p % 2) := by
  rcases Nat.mod_two_eq_zero_or_one p with h | h
  · rw [if_pos h, h]
  · rw [if_neg (by omega), h]

theorem tSel_step (c q : P5) (k p : ℕ) : tSel (stepq c q k) p = tNext c q k p :=
  (sel01 (tNext c q k) p).trans (tNext_mod c q k p)

theorem lSel_step (c q : P5) (k p : ℕ) : lSel (stepq c q k) p = lNext c q k (p % 2) :=
  sel01 (lNext c q k) p

/-- q holds level k. -/
def Inv (k : ℕ) (q : P5) : Prop :=
  q.2.2.2.2 = P k % Mn ∧
  (∀ x, Stab x → T k (3 * x + 2 - k) (s k) % Mn = lSel q x) ∧
  (1 ≤ k → ∀ x, Stab x → T k 1 x % Mn = tSel q x)

theorem st_zero : st par0 0 = (0, 0, T0R (xr 0) (xr 1), T0R (xr 1) (xr 0), 0) := by
  show ((0, 0, T0R (xs par0 0) (xs par0 1), T0R (xs par0 1) (xs par0 0), 0) : P5) = _
  rw [xs_par0, xs_par0]

theorem inv_zero : Inv 0 (st par0 0) := by
  rw [st_zero]
  unfold Inv
  refine ⟨?_, ?_, ?_⟩
  · show 0 = P 0 % Mn
    rw [P_zero, Nat.zero_mod]
  · intro x hx
    show T 0 (3 * x + 2) 1 % Mn = if x % 2 = 0 then T0R (xr 0) (xr 1) else T0R (xr 1) (xr 0)
    rw [stab_T0 hx]
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · rw [if_pos h, h, show (x + 1) % 2 = 1 by omega]
    · rw [if_neg (by omega), h, show (x + 1) % 2 = 0 by omega]
  · intro h; omega

theorem tNext_ok (k : ℕ) (q : P5) (hk : k ≤ 19) (hInv : Inv k q) {x : ℕ} (hx : Stab x) :
    T (k + 1) 1 x % Mn = tNext par0 q k x := by
  unfold Inv at hInv
  obtain ⟨hP, hL, _⟩ := hInv
  have hxD := stab_ge hx
  unfold tNext
  rw [xs_par0, ← xr_mod x, ← stab_res hx, Nat.mod_mod_of_dvd _ Mn_dvd_Q, hP, ← hL x hx,
    ← cB_mod x (k + 1) (by omega) (by omega), T_succ_one]
  unfold sterm
  exact add3_mod _ _ _ _

theorem pr_add {pr Pk Tk add : ℕ} (hP : pr = Pk % Mn) (h : Tk % Mn = add % Mn) :
    (pr + add) % Mn = (Pk + Tk) % Mn := by
  subst hP
  exact (Nat.mod_modEq Pk Mn).add h.symm

theorem s_stab (k : ℕ) (hk : 3 ≤ k) (hk21 : k ≤ 21) : Stab (s k) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [s_succ]
  exact tall j (by omega) (by omega) (s j) (s_big j (by omega))

theorem T1_one_six : T 1 1 (s 1) = 1050 + T0x 20 := by
  have c : cB 6 1 = 1050 := by unfold cB costB; norm_num
  have t : T 1 1 6 = sterm 0 6 := T_succ_one 0 6
  have e : sterm 0 6 = cB 6 1 + T 0 20 1 := sterm0_eq 6
  rw [s_one, t, e, c, T0_exact]

theorem prNext_ok (k : ℕ) (q : P5) (hk : k ≤ 19) (hInv : Inv k q) : prNext par0 q k = P (k + 1) % Mn := by
  unfold Inv at hInv
  obtain ⟨hP, _, hT⟩ := hInv
  unfold prNext
  rw [P_succ]
  refine pr_add hP ?_
  by_cases h0 : k = 0
  · subst h0
    rw [if_pos rfl, s_zero, T0_one, cD_one]
  · by_cases h1 : k = 1
    · subst h1
      rw [if_neg h0, if_pos rfl, T1_one_six]
    · by_cases h2 : k = 2
      · subst h2
        have t : T 2 1 (s 2) = sterm 1 8716961001 := by
          rw [s_two]
          exact T_succ_one 1 8716961001
        rw [if_neg h0, if_neg h1, if_pos rfl, t, sterm1_res _ (by norm_num), term2x_mod]
      · rw [if_neg h0, if_neg h1, if_neg h2]
        have e : T k 1 (s k) % Mn = tSel q (k + 1) :=
          (hT (by omega) (s k) (s_stab k (by omega) (by omega))).trans (tSel_congr q (s_parity k))
        rw [← e, Nat.mod_mod]

theorem lNext_zero (q : P5) {x : ℕ} (hx : Stab x) :
    T 1 (3 * x + 2 - 1) (s 1) % Mn = lNext par0 q 0 (x % 2) := by
  have hxD := stab_ge hx
  unfold lNext
  rw [if_pos rfl, nS_eq hx 1 (by norm_num) (by omega), s_one, L1_eq _ (by omega)]

theorem iter_stab (k : ℕ) (hk : 2 ≤ k) (hk20 : k ≤ 20) {z : ℕ} (hz : Stab z) :
    ∀ i, Stab ((V k)^[i] z) := by
  intro i
  induction i with
  | zero => exact hz
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact tall k hk hk20 _ (by have := stab_ge ih; have hD : D = 204 := D_def; omega)

/-- The level-2 summands along V_2^i(s_2), mod Mn. -/
def g2 (q : P5) (i : ℕ) : ℕ := if i = 0 then term2x par0 8716961001 else tNext par0 q 1 (i + 1)

theorem g2_zero (q : P5) : g2 q 0 = term2x par0 8716961001 := by unfold g2; rw [if_pos rfl]

theorem g2_succ (q : P5) (i : ℕ) : g2 q (i + 1) = tNext par0 q 1 (i + 1 + 1) := by
  unfold g2; rw [if_neg (by omega)]

theorem g2_mod (q : P5) (i : ℕ) : g2 q i % Mn = g2 q i := by
  unfold g2
  by_cases h : i = 0
  · rw [if_pos h, term2x_mod]
  · rw [if_neg h, tNext_modMn]

theorem g2_period (q : P5) (i : ℕ) (hi : 2 ≤ i) : g2 q (i + 2) = g2 q i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [show j + 1 + 2 = (j + 2) + 1 by ring, g2_succ, g2_succ]
  exact tNext_congr par0 q 1 (by omega)

theorem g2_res (q : P5) (hInv : Inv 1 q) (i : ℕ) : sterm 1 ((V 2)^[i] (s 2)) % Mn = g2 q i := by
  cases i with
  | zero =>
    rw [g2_zero, Function.iterate_zero_apply, s_two, sterm1_res _ (by norm_num)]
  | succ j =>
    rw [g2_succ]
    have hy : Stab ((V 2)^[j + 1] (s 2)) := by
      rw [Function.iterate_succ_apply, ← s_succ 2]
      exact iter_stab 2 le_rfl (by norm_num) (s_stab 3 le_rfl (by norm_num)) j
    have hp : (V 2)^[j + 1] (s 2) % 2 = (j + 1 + 1) % 2 := by
      have hs2 := s_ge 2
      have hpar := s_parity 2
      rw [iter_parity 2 (parity 2).1 (s 2) (by omega) (j + 1)]
      omega
    rw [← T_succ_one 1, tNext_ok 1 q (by norm_num) hInv hy]
    exact tNext_congr par0 q 1 hp

theorem lNext_one (q : P5) (hInv : Inv 1 q) {x : ℕ} (hx : Stab x) :
    T 2 (3 * x + 2 - 2) (s 2) % Mn = lNext par0 q 1 (x % 2) := by
  have hMb := Mn_big
  have hxD := stab_ge hx
  obtain ⟨n, hn⟩ : ∃ n, 3 * x + 2 - 2 = 2 + n := ⟨3 * x - 2, by omega⟩
  have e0 : T 2 (3 * x + 2 - 2) (s 2) = sumF (fun i => sterm 1 ((V 2)^[i] (s 2))) (3 * x + 2 - 2) :=
    T_succ_eq 1 _ _
  have e1 : sumF (fun i => sterm 1 ((V 2)^[i] (s 2))) (3 * x + 2 - 2) % Mn =
      sumF (g2 q) (3 * x + 2 - 2) % Mn :=
    sumF_mod _ (g2 q) Mn (fun i => by
      show sterm 1 ((V 2)^[i] (s 2)) % Mn = g2 q i % Mn
      rw [g2_res q hInv i, g2_mod]) _
  have e2 := sum_alt (g2 q) 2 (g2_period q) n
  have a0 : sumF (g2 q) 2 = term2x par0 8716961001 + tNext par0 q 1 0 := by
    show 0 + g2 q 0 + g2 q (0 + 1) = _
    rw [Nat.zero_add (g2 q 0), g2_zero, g2_succ q 0,
      tNext_congr par0 q 1 (show (0 + 1 + 1) % 2 = 0 % 2 by norm_num)]
  have a2 : g2 q 2 = tNext par0 q 1 1 :=
    (g2_succ q 1).trans (tNext_congr par0 q 1 (by norm_num))
  have a3 : g2 q (2 + 1) = tNext par0 q 1 0 :=
    (g2_succ q 2).trans (tNext_congr par0 q 1 (by norm_num))
  have c1 : (n + 1) / 2 % Mn = hm (nS par0 2 (x % 2) + 2 * Mn - 1) := by
    rw [nS_eq hx 2 (by norm_num) (by omega), hm_sub _ 1 (by omega) (by omega), hn,
      show 2 + n - 1 = n + 1 by omega]
  have c2 : n / 2 % Mn = hm (nS par0 2 (x % 2) + 2 * Mn - 2) := by
    rw [nS_eq hx 2 (by norm_num) (by omega), hm_sub _ 2 (by omega) (by omega), hn,
      show 2 + n - 2 = n by omega]
  rw [e0, e1, hn, e2, a0, a2, a3]
  unfold lNext
  rw [if_neg (by norm_num), if_pos rfl, ← c1, ← c2]
  exact ((Nat.ModEq.refl _).add ((Nat.mod_modEq _ Mn).symm.mul_right _)).add
    ((Nat.mod_modEq _ Mn).symm.mul_right _)

theorem lNext_big (k : ℕ) (hk2 : 2 ≤ k) (hk18 : k ≤ 18) (q : P5) (hInv : Inv k q) {x : ℕ} (hx : Stab x) :
    T (k + 1) (3 * x + 2 - (k + 1)) (s (k + 1)) % Mn = lNext par0 q k (x % 2) := by
  have hMb := Mn_big
  have hxD := stab_ge hx
  have hs : Stab (s (k + 1)) := s_stab (k + 1) (by omega) (by omega)
  have hres : ∀ i, sterm k ((V (k + 1))^[i] (s (k + 1))) % Mn = tNext par0 q k (k + i) % Mn := by
    intro i
    have hy := iter_stab (k + 1) (by omega) (by omega) hs i
    have hp : (V (k + 1))^[i] (s (k + 1)) % 2 = (k + i) % 2 := by
      have hs1 := s_ge (k + 1)
      have hpar := s_parity (k + 1)
      rw [iter_parity (k + 1) (parity (k + 1)).1 (s (k + 1)) (by omega) i]
      omega
    rw [← T_succ_one k, tNext_ok k q (by omega) hInv hy, tNext_congr par0 q k hp, tNext_modMn]
  have e0 : T (k + 1) (3 * x + 2 - (k + 1)) (s (k + 1)) % Mn =
      sumF (fun i => tNext par0 q k (k + i)) (3 * x + 2 - (k + 1)) % Mn := by
    rw [T_succ_eq]
    exact sumF_mod _ _ Mn hres _
  have e2 := sum_alt0 (fun i => tNext par0 q k (k + i))
    (fun i => tNext_congr par0 q k (by omega)) (3 * x + 2 - (k + 1))
  have c1 : (3 * x + 2 - (k + 1) + 1) / 2 % Mn = hm (nS par0 (k + 1) (x % 2) + 1) := by
    rw [nS_eq hx (k + 1) (by omega) (by omega), hm_add]
  have c2 : (3 * x + 2 - (k + 1)) / 2 % Mn = hm (nS par0 (k + 1) (x % 2)) := by
    rw [nS_eq hx (k + 1) (by omega) (by omega), hm_self]
  rw [e0, e2]
  unfold lNext
  rw [if_neg (by omega), if_neg (by omega), ← c1, ← c2]
  exact ((Nat.mod_modEq _ Mn).symm.mul_right _).add ((Nat.mod_modEq _ Mn).symm.mul_right _)

theorem inv_step (k : ℕ) (hk : k ≤ 18) (q : P5) (hInv : Inv k q) : Inv (k + 1) (stepq par0 q k) := by
  unfold Inv
  refine ⟨?_, ?_, ?_⟩
  · exact prNext_ok k q (by omega) hInv
  · intro x hx
    rw [lSel_step]
    by_cases h0 : k = 0
    · subst h0
      exact lNext_zero q hx
    · by_cases h1 : k = 1
      · subst h1
        exact lNext_one q hInv hx
      · exact lNext_big k (by omega) hk q hInv hx
  · intro _ x hx
    rw [tSel_step]
    exact tNext_ok k q (by omega) hInv hx

/-- Every level to 19. -/
theorem st_ok (k : ℕ) (hk : k ≤ 19) : Inv k (st par0 k) := by
  induction k with
  | zero => exact inv_zero
  | succ k ih => exact inv_step k (by omega) (st par0 k) (ih (by omega))

theorem Acc_succ (i : ℕ) : Acc (i + 1) = V (i + 1) (Acc i) := rfl

theorem Acc_parity (i : ℕ) : Acc i % 2 = i % 2 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h := Acc_ge i
    rw [Acc_succ, V_parity (i + 1) (Acc i) (by omega)]
    omega

theorem Acc_big (i : ℕ) (hi : 1 ≤ i) : 204 ≤ Acc i := by
  induction i, hi using Nat.le_induction with
  | base => rw [Acc_one]; norm_num
  | succ i _ ih =>
    have h := V_ge (i + 1) (Acc i)
    rw [Acc_succ]
    omega

theorem Acc_stab (i : ℕ) (hi : 2 ≤ i) (hi20 : i ≤ 20) : Stab (Acc i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [Acc_succ]
  exact tall (j + 1) (by omega) (by omega) (Acc j)
    (by have := Acc_big j (by omega); have hD : D = 204 := D_def; omega)

theorem Acc19_mod : Acc 19 % Mn = xr 1 % Mn := by
  have h := stab_res (Acc_stab 19 (by norm_num) (by norm_num))
  have h19 : Acc 19 % 2 = 1 := by have := Acc_parity 19; omega
  rw [h19] at h
  rw [← Nat.mod_mod_of_dvd (Acc 19) Mn_dvd_Q, h]

/-- The summands of τ at positions 3 … 19, mod Mn. -/
def topSum (c : P5) : ℕ := sumF (fun j => tSel (st c (j + 3)) j) 17

theorem topSum_expand (c : P5) : topSum c = 0 + tSel (st c 3) 0 + tSel (st c 4) 1 + tSel (st c 5) 2 +
    tSel (st c 6) 3 + tSel (st c 7) 4 + tSel (st c 8) 5 + tSel (st c 9) 6 + tSel (st c 10) 7 +
    tSel (st c 11) 8 + tSel (st c 12) 9 + tSel (st c 13) 10 + tSel (st c 14) 11 + tSel (st c 15) 12 +
    tSel (st c 16) 13 + tSel (st c 17) 14 + tSel (st c 18) 15 + tSel (st c 19) 16 := rfl

/-- τ mod Mn from the five numbers. -/
def tauModP (c : P5) : ℕ :=
  (3959 + ((1566 + T0x 26) + term2x c 6354664570821 + topSum c) +
    (48 * (c.2.1 % Mn) * (c.2.1 % Mn) + 198 * (c.2.1 % Mn) + Mn - 456) % Mn) % Mn

/-- σ mod Mn from the five numbers. -/
def sigmaModP (c : P5) : ℕ := (6 * (c.2.1 % Mn) + 7) % Mn

theorem G0 : T 1 1 (Acc 0) = 1566 + T0x 26 := by
  have c : cB 8 1 = 1566 := by unfold cB costB; norm_num
  have t : T 1 1 8 = sterm 0 8 := T_succ_one 0 8
  have e : sterm 0 8 = cB 8 1 + T 0 26 1 := sterm0_eq 8
  show T 1 1 8 = _
  rw [t, e, c, T0_exact]

theorem G1 : T 2 1 (Acc 1) % Mn = term2x par0 6354664570821 := by
  have t : T 2 1 6354664570821 = sterm 1 6354664570821 := T_succ_one 1 _
  rw [Acc_one, t, sterm1_res _ (by norm_num)]

theorem Gj (j : ℕ) (hj : j ≤ 16) : T (j + 3) 1 (Acc (j + 2)) % Mn = tSel (st par0 (j + 3)) j := by
  have hI := st_ok (j + 3) (by omega)
  unfold Inv at hI
  obtain ⟨_, _, hT⟩ := hI
  rw [hT (by omega) (Acc (j + 2)) (Acc_stab (j + 2) (by omega) (by omega))]
  exact tSel_congr _ (by have := Acc_parity (j + 2); omega)

theorem ladder_split (F : ℕ → ℕ → ℕ → ℕ) (A : ℕ → ℕ) : sumF (fun i => F (i + 1) 1 (A i)) 19 =
    F 1 1 (A 0) + F 2 1 (A 1) + sumF (fun j => F (j + 3) 1 (A (j + 2))) 17 :=
  sumF_shift2 (fun i => F (i + 1) 1 (A i)) 17

theorem split_gen (F : ℕ → ℕ → ℕ → ℕ) (A : ℕ → ℕ) (c : ℕ) :
    3959 + ∑ i ∈ range 19, F (i + 1) 1 (A i) + c =
      3959 + (F 1 1 (A 0) + F 2 1 (A 1) + sumF (fun j => F (j + 3) 1 (A (j + 2))) 17) + c := by
  have e : ∑ i ∈ range 19, F (i + 1) 1 (A i) = sumF (fun i => F (i + 1) 1 (A i)) 19 :=
    (sumF_eq _ 19).symm
  rw [e, ladder_split]

theorem tau_split : tau = 3959 + (T 1 1 (Acc 0) + T 2 1 (Acc 1) +
    sumF (fun j => T (j + 3) 1 (Acc (j + 2))) 17) + costE (Acc 19 - 7) := by
  rw [tau_tauF, tauF_eq]
  exact split_gen T Acc (costE (Acc 19 - 7))

theorem costE_res : costE (Acc 19 - 7) % Mn =
    (48 * (xr 1 % Mn) * (xr 1 % Mn) + 198 * (xr 1 % Mn) + Mn - 456) % Mn := by
  have hMb := Mn_big
  have hA := Acc_ge 19
  obtain ⟨m, hA7⟩ : ∃ m, Acc 19 = m + 7 := ⟨Acc 19 - 7, by omega⟩
  have e : costE (Acc 19 - 7) + 456 = 48 * Acc 19 * Acc 19 + 198 * Acc 19 := by
    rw [hA7, Nat.add_sub_cancel]
    unfold costE
    ring
  have h : Acc 19 ≡ xr 1 % Mn [MOD Mn] := modeq_of_mod Acc19_mod
  refine modEq_sub_of (by omega) ?_
  rw [e]
  exact ((h.mul_left 48).mul h).add (h.mul_left 198)

theorem modeq_of_eq {a b : ℕ} (h : a = b) : a ≡ b [MOD Mn] := by
  subst h; exact Nat.ModEq.refl _

theorem assemble {a0 b0 a1 b1 a2 b2 a3 b3 : ℕ} (h0 : a0 ≡ b0 [MOD Mn]) (h1 : a1 ≡ b1 [MOD Mn])
    (h2 : a2 ≡ b2 [MOD Mn]) (h3 : a3 ≡ b3 [MOD Mn]) :
    (3959 + (a0 + a1 + a2) + a3) % Mn = (3959 + (b0 + b1 + b2) + b3) % Mn :=
  ((Nat.ModEq.refl 3959).add ((h0.add h1).add h2)).add h3

theorem tauModP_unfold (c : P5) : tauModP c =
    (3959 + ((1566 + T0x 26) + term2x c 6354664570821 + sumF (fun j => tSel (st c (j + 3)) j) 17) +
      (48 * (c.2.1 % Mn) * (c.2.1 % Mn) + 198 * (c.2.1 % Mn) + Mn - 456) % Mn) % Mn := rfl

/-- τ mod 10^200 is the evaluator's value at the five numbers. -/
theorem tau_mod : tau % Mn = tauModP par0 := by
  have s17 : sumF (fun j => T (j + 3) 1 (Acc (j + 2))) 17 ≡
      sumF (fun j => tSel (st par0 (j + 3)) j) 17 [MOD Mn] :=
    sumF_mod_lt (fun j => T (j + 3) 1 (Acc (j + 2))) (fun j => tSel (st par0 (j + 3)) j) Mn 17 (fun j hj => by
      show T (j + 3) 1 (Acc (j + 2)) % Mn = tSel (st par0 (j + 3)) j % Mn
      rw [← Gj j (by omega), Nat.mod_mod])
  have g0 : T 1 1 (Acc 0) ≡ 1566 + T0x 26 [MOD Mn] := modeq_of_eq G0
  have g1 : T 2 1 (Acc 1) ≡ term2x par0 6354664570821 [MOD Mn] := modeq_of_mod G1
  have ce : costE (Acc 19 - 7) ≡
      (48 * (par0.2.1 % Mn) * (par0.2.1 % Mn) + 198 * (par0.2.1 % Mn) + Mn - 456) % Mn [MOD Mn] := by
    rw [par0_x1]
    exact modeq_of_mod costE_res
  have key := assemble g0 g1 s17 ce
  rw [← tau_split] at key
  rw [key, tauModP_unfold]

/-- σ mod 10^200 is the evaluator's value at the five numbers. -/
theorem sigma_mod : sigma % Mn = sigmaModP par0 := by
  have h : Acc 19 ≡ xr 1 % Mn [MOD Mn] := modeq_of_mod Acc19_mod
  rw [sigma_sigF, sigF_eq]
  unfold sigmaModP
  rw [par0_x1]
  exact (h.mul_left 6).add_right 7

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.T0_res
#print axioms BeaverStructural.BB7b.L1_eq
#print axioms BeaverStructural.BB7b.st_ok
#print axioms BeaverStructural.BB7b.tau_mod
#print axioms BeaverStructural.BB7b.sigma_mod
