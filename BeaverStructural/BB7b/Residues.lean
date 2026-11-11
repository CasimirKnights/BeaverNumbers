import BeaverStructural.BB7b.Numbers
import BeaverStructural.BB7.ResiduesTall

/-! Residues for the clock of the BB(7) machine of October 2026.
V_1(x) = (5·3^(3x+2) − 3)/2 (`V1_form`); T_0(n, 1) in closed form (`T0_closed`).
With Q b = 4·10^b: 3^(Q b) ≡ 1 (mod 2·Q (b+1)) (`three_cycle`), so V_1(x) mod Q (b+1) is a function of x mod Q b
(`v1_mod`); V_1(x) mod 4 is 2 for odd x and 1 for even x (`V1_mod4`), and V_1 flips parity.
`R i b` = V_1^i(6) mod Q b (`R_eq`), of period 2 in i from i = b on (`R_period`); a V_1-iterate of height above b has
its residue mod Q b fixed by its parity (`stable_val`).  V_k(x), k ≥ 2, x ≥ 204, is such an iterate of height 204
(`tall`), and every V_k flips parity (`parity`). -/

namespace BeaverStructural.BB7b

open Finset
open BeaverStructural.BB7 (md md_pos powMod powMod_eq sumF sumF_eq)

theorem two_iter (n : ℕ) : ∀ a, 2 * (V 0)^[n] a + 3 = 3 ^ n * (2 * a + 3) := by
  induction n with
  | zero => intro a; simp
  | succ n ih =>
    intro a
    rw [Function.iterate_succ_apply, ih, V_zero, pow_succ]
    ring

/-- 2·V_1(x) + 3 = 5·3^(3x+2). -/
theorem V1_form (x : ℕ) : 2 * V 1 x + 3 = 5 * 3 ^ (3 * x + 2) := by
  show 2 * (V 0)^[3 * x + 2] 1 + 3 = 5 * 3 ^ (3 * x + 2)
  rw [two_iter]
  ring

/-- 8·T_0(n, a) + 112n + 3C² + 60C = 3C²·9^n + 60C·3^n, C = 2a + 3. -/
theorem T0_closed_gen (n : ℕ) : ∀ a, 8 * T 0 n a + 112 * n + 3 * (2 * a + 3) ^ 2 + 60 * (2 * a + 3) =
    3 * (2 * a + 3) ^ 2 * 9 ^ n + 60 * (2 * a + 3) * 3 ^ n := by
  induction n with
  | zero => intro a; rw [T_none]; ring
  | succ n ih =>
    intro a
    have h := ih (3 * a + 3)
    rw [T_zero_succ, V_zero, pow_succ 9 n, pow_succ 3 n]
    unfold cD
    generalize T 0 n (3 * a + 3) = t at h ⊢
    generalize (9 : ℕ) ^ n = Y at h ⊢
    generalize (3 : ℕ) ^ n = Z at h ⊢
    zify at h ⊢
    linear_combination h

/-- 8·T_0(n, 1) + 112n + 375 = 75·9^n + 300·3^n. -/
theorem T0_closed (n : ℕ) : 8 * T 0 n 1 + 112 * n + 375 = 75 * 9 ^ n + 300 * 3 ^ n := by
  have h := T0_closed_gen n 1
  norm_num at h
  omega

/-- T_0(n, 1) as a number. -/
def T0x (n : ℕ) : ℕ := (75 * 9 ^ n + 300 * 3 ^ n - 112 * n - 375) / 8

theorem T0_exact (n : ℕ) : T 0 n 1 = T0x n := by
  have h := T0_closed n
  unfold T0x
  omega

theorem sq_lift (x j : ℕ) (hj : 1 ≤ j) (h : x ≡ 1 [MOD 2 ^ j]) : x ^ 2 ≡ 1 [MOD 2 ^ (j + 1)] := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h1 : ((2 ^ (j' + 1) : ℕ) : ℤ) ∣ (x : ℤ) - (1 : ℕ) := (Nat.modEq_iff_dvd.1 h.symm)
  obtain ⟨t, ht⟩ := h1
  refine (Nat.modEq_iff_dvd.2 ?_).symm
  refine ⟨t + 2 ^ j' * t ^ 2, ?_⟩
  push_cast at ht ⊢
  have hx : (x : ℤ) = 1 + 2 ^ (j' + 1) * t := by linarith
  rw [hx]
  ring

/-- 3^(2^(k+1)) ≡ 1 (mod 2^(k+3)). -/
theorem three_pow_two (k : ℕ) : 3 ^ 2 ^ (k + 1) ≡ 1 [MOD 2 ^ (k + 3)] := by
  induction k with
  | zero => decide
  | succ k ih =>
    have := sq_lift _ (k + 3) (by omega) ih
    rw [← pow_mul, ← pow_succ] at this
    exact this

/-- Q b = 4·10^b. -/
def Q (b : ℕ) : ℕ := md (b + 2) b

theorem Q_ge (b : ℕ) : 4 ≤ Q b := by
  unfold Q md
  have h1 : 4 ≤ 2 ^ (b + 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (b + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 1 ≤ 5 ^ b := Nat.one_le_pow _ _ (by norm_num)
  nlinarith

theorem Q_succ (b : ℕ) : Q (b + 1) = 10 * Q b := by
  unfold Q md; ring

theorem Q_zero : Q 0 = 4 := by unfold Q md; norm_num

/-- 3^(Q b) ≡ 1 (mod 2·Q (b+1)). -/
theorem three_cycle (b : ℕ) : 3 ^ Q b ≡ 1 [MOD 2 * Q (b + 1)] := by
  have h2 : 3 ^ Q b ≡ 1 [MOD 2 ^ (b + 4)] := by
    have := (three_pow_two (b + 1)).pow (5 ^ b)
    rw [← pow_mul, one_pow] at this
    exact this
  have h5 : 3 ^ Q b ≡ 1 [MOD 5 ^ (b + 1)] := by
    have hcop : Nat.Coprime 3 (5 ^ (b + 1)) := Nat.Coprime.pow_right _ (by norm_num)
    have ht := Nat.ModEq.pow_totient hcop
    rw [Nat.totient_prime_pow_succ Nat.prime_five] at ht
    have := ht.pow (2 ^ b)
    rw [← pow_mul, one_pow] at this
    have e : Q b = 5 ^ b * (5 - 1) * 2 ^ b := by unfold Q md; ring
    rw [e]
    exact this
  have hcop : Nat.Coprime (2 ^ (b + 4)) (5 ^ (b + 1)) := Nat.Coprime.pow _ _ (by norm_num)
  have e : 2 * Q (b + 1) = 2 ^ (b + 4) * 5 ^ (b + 1) := by unfold Q md; ring
  rw [e]
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h2, h5⟩

/-- V_1(x) mod Q (b+1) from x mod Q b. -/
def v1step (r b : ℕ) : ℕ :=
  ((5 * powMod 3 (3 * r + 2) (2 * Q (b + 1)) + 2 * Q (b + 1) - 3) % (2 * Q (b + 1))) / 2

theorem v1_mod (x b : ℕ) : V 1 x % Q (b + 1) = v1step (x % Q b) b := by
  unfold v1step
  rw [powMod_eq]
  have hm4 := Q_ge (b + 1)
  obtain ⟨m, hm⟩ : ∃ m, m = Q (b + 1) := ⟨_, rfl⟩
  rw [← hm] at hm4 ⊢
  obtain ⟨r, hr⟩ : ∃ r, r = x % Q b := ⟨_, rfl⟩
  rw [← hr]
  have F := V1_form x
  have hx : 3 * x + 2 = Q b * (3 * (x / Q b)) + (3 * r + 2) := by
    have h := Nat.div_add_mod x (Q b)
    calc 3 * x + 2 = 3 * (Q b * (x / Q b) + x % Q b) + 2 := by rw [h]
      _ = Q b * (3 * (x / Q b)) + (3 * r + 2) := by rw [hr]; ring
  have cyc : 3 ^ (3 * x + 2) ≡ 3 ^ (3 * r + 2) [MOD 2 * m] := by
    rw [hx, pow_add, pow_mul, hm]
    have := ((three_cycle b).pow (3 * (x / Q b))).mul_right (3 ^ (3 * r + 2))
    rw [one_pow, one_mul] at this
    exact this
  have c2 : 5 * 3 ^ (3 * x + 2) ≡ 5 * (3 ^ (3 * r + 2) % (2 * m)) [MOD 2 * m] :=
    (cyc.trans (Nat.mod_modEq _ _).symm).mul_left 5
  have hge : 3 ≤ 5 * (3 ^ (3 * r + 2) % (2 * m)) + 2 * m := by omega
  have c3 : 2 * V 1 x + 3 ≡ (5 * (3 ^ (3 * r + 2) % (2 * m)) + 2 * m - 3) + 3 [MOD 2 * m] := by
    rw [F, Nat.sub_add_cancel hge]
    refine c2.trans ?_
    show _ % (2 * m) = _ % (2 * m)
    rw [Nat.add_mod_right]
  have h2v : (2 * V 1 x) % (2 * m) = (5 * (3 ^ (3 * r + 2) % (2 * m)) + 2 * m - 3) % (2 * m) :=
    Nat.ModEq.add_right_cancel' 3 c3
  rw [← h2v, Nat.mul_mod_mul_left, Nat.mul_div_cancel_left _ (by norm_num)]

theorem three_pow_mod8 (E : ℕ) : 3 ^ E % 8 = if E % 2 = 0 then 1 else 3 := by
  have h9 : ∀ j, (3 ^ 2) ^ j % 8 = 1 := by
    intro j
    rw [Nat.pow_mod]
    norm_num
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' E
  · have h : E % 2 = 0 := by omega
    rw [if_pos h, hj, pow_mul, h9]
  · have h : ¬ E % 2 = 0 := by omega
    rw [if_neg h, hj, pow_succ, pow_mul, Nat.mul_mod, h9]

/-- V_1(x) mod 4: 2 for odd x, 1 for even x. -/
theorem V1_mod4 (x : ℕ) : V 1 x % 4 = if x % 2 = 1 then 2 else 1 := by
  have F := V1_form x
  have h8 := three_pow_mod8 (3 * x + 2)
  have hm : (2 * V 1 x + 3) % 8 = 5 * (3 ^ (3 * x + 2) % 8) % 8 := by
    rw [F, Nat.mul_mod]
  by_cases hx : x % 2 = 1
  · have he : ¬ (3 * x + 2) % 2 = 0 := by omega
    rw [if_neg he] at h8
    rw [h8] at hm
    rw [if_pos hx]
    omega
  · have he : (3 * x + 2) % 2 = 0 := by omega
    rw [if_pos he] at h8
    rw [h8] at hm
    rw [if_neg hx]
    omega

theorem V1_parity (x : ℕ) : V 1 x % 2 = (x + 1) % 2 := by
  have h := V1_mod4 x
  by_cases hx : x % 2 = 1
  · rw [if_pos hx] at h; omega
  · rw [if_neg hx] at h; omega

/-- `R i b` = V_1^i(6) mod Q b. -/
def R : ℕ → ℕ → ℕ
  | i, 0 => if i % 2 = 0 then 2 else 1
  | 0, _ + 1 => 6
  | i + 1, b + 1 => v1step (R i b) b

theorem R_zero (i : ℕ) : R i 0 = if i % 2 = 0 then 2 else 1 := by
  cases i <;> rfl

theorem iter6_mod4 (i : ℕ) : (V 1)^[i] 6 % 4 = if i % 2 = 0 then 2 else 1 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', V1_mod4]
    by_cases hi : i % 2 = 0
    · rw [if_pos hi] at ih
      have h1 : ¬ ((V 1)^[i] 6 % 2 = 1) := by omega
      have h2 : ¬ ((i + 1) % 2 = 0) := by omega
      rw [if_neg h1, if_neg h2]
    · rw [if_neg hi] at ih
      have h1 : (V 1)^[i] 6 % 2 = 1 := by omega
      have h2 : (i + 1) % 2 = 0 := by omega
      rw [if_pos h1, if_pos h2]

theorem R_eq : ∀ b i, (V 1)^[i] 6 % Q b = R i b := by
  intro b
  induction b with
  | zero =>
    intro i
    rw [Q_zero, iter6_mod4]
    cases i <;> rfl
  | succ b ih =>
    intro i
    cases i with
    | zero =>
      show 6 % Q (b + 1) = 6
      have := Q_succ b
      have := Q_ge b
      exact Nat.mod_eq_of_lt (by omega)
    | succ i =>
      rw [Function.iterate_succ_apply', v1_mod, ih i]
      rfl

theorem R_period : ∀ b i, b ≤ i → R (i + 2) b = R i b := by
  intro b
  induction b with
  | zero =>
    intro i _
    rw [R_zero, R_zero, Nat.add_mod_right]
  | succ b ih =>
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    show v1step (R (j + 2) b) b = v1step (R j b) b
    rw [ih j (by omega)]

theorem R_add (b i : ℕ) (hi : b ≤ i) : ∀ t, R (i + 2 * t) b = R i b := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [show i + 2 * (t + 1) = (i + 2 * t) + 2 by ring, R_period b _ (by omega), ih]

theorem R_class (b i j : ℕ) (hi : b ≤ i) (hj : b ≤ j) (h : i % 2 = j % 2) : R i b = R j b := by
  rcases le_total i j with hij | hij
  · obtain ⟨t, rfl⟩ : ∃ t, j = i + 2 * t := ⟨(j - i) / 2, by omega⟩
    exact (R_add b i hi t).symm
  · obtain ⟨t, rfl⟩ : ∃ t, i = j + 2 * t := ⟨(i - j) / 2, by omega⟩
    exact R_add b j hj t

/-- The residue mod Q b of a V_1-iterate of height above b and parity p. -/
def Om (b p : ℕ) : ℕ := R (2 * b + 2 + p % 2) b

theorem stable_aux : ∀ b d w, b + 1 ≤ d →
    ∃ j, b ≤ j ∧ j % 2 = (V 1)^[d] w % 2 ∧ (V 1)^[d] w % Q b = R j b := by
  intro b
  induction b with
  | zero =>
    intro d w hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [Function.iterate_succ_apply']
    have h4 := V1_mod4 ((V 1)^[d'] w)
    refine ⟨V 1 ((V 1)^[d'] w) % 2, Nat.zero_le _, Nat.mod_mod _ _, ?_⟩
    rw [Q_zero]
    rw [R_zero]
    by_cases hx : (V 1)^[d'] w % 2 = 1
    · rw [if_pos hx] at h4
      have : V 1 ((V 1)^[d'] w) % 2 % 2 = 0 := by omega
      rw [if_pos this, h4]
    · rw [if_neg hx] at h4
      have : ¬ V 1 ((V 1)^[d'] w) % 2 % 2 = 0 := by omega
      rw [if_neg this, h4]
  | succ b ih =>
    intro d w hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨j, hj, hp, hr⟩ := ih d' w (by omega)
    rw [Function.iterate_succ_apply']
    refine ⟨j + 1, by omega, ?_, ?_⟩
    · rw [V1_parity]; omega
    · rw [v1_mod, hr]; rfl

theorem stable_val (b d w : ℕ) (hd : b + 1 ≤ d) : (V 1)^[d] w % Q b = Om b ((V 1)^[d] w % 2) := by
  obtain ⟨j, hj, hp, hr⟩ := stable_aux b d w hd
  rw [hr]
  unfold Om
  exact R_class b _ _ hj (by omega) (by omega)

/-- The height above which a V_1-iterate is stable at every modulus used. -/
irreducible_def D : ℕ := 204

/-- x is a V_1-iterate of height D. -/
def Stab (x : ℕ) : Prop := ∃ w, x = (V 1)^[D] w

theorem stab_mod {x : ℕ} (hx : Stab x) (b : ℕ) (hb : b + 1 ≤ D) : x % Q b = Om b (x % 2) := by
  obtain ⟨w, rfl⟩ := hx
  exact stable_val b D w hb

theorem stab_V1 {x : ℕ} (hx : Stab x) : Stab (V 1 x) := by
  obtain ⟨w, rfl⟩ := hx
  exact ⟨V 1 w, (Function.iterate_succ_apply' (V 1) D w).symm.trans (Function.iterate_succ_apply (V 1) D w)⟩

theorem s_one : s 1 = 6 := rfl

theorem s_two : s 2 = 8716961001 := by
  have h := V1_form 6
  have e : s 2 = V 1 6 := rfl
  rw [e]
  norm_num at h
  omega

theorem Acc_one : Acc 1 = 6354664570821 := by
  have h := V1_form 8
  have e : Acc 1 = V 1 8 := rfl
  rw [e]
  norm_num at h
  omega

theorem s_mono (k : ℕ) : s k + 1 ≤ s (k + 1) := by
  rw [s_succ]; exact V_ge k (s k)

theorem s_big : ∀ k, 2 ≤ k → D ≤ s k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rw [s_two, D_def]; norm_num
  | succ k _ ih => have := s_mono k; omega

theorem tall2 (x : ℕ) (hx : D ≤ 3 * x + 1) : Stab (V 2 x) := by
  refine ⟨(V 1)^[3 * x + 1 - D] (s 1), ?_⟩
  rw [V_succ, ← Function.iterate_add_apply]
  congr 1
  omega

/-- V_k(x) is a V_1-iterate of height D, 2 ≤ k ≤ 20, x ≥ D. -/
theorem tall : ∀ k, 2 ≤ k → k ≤ 20 → ∀ x, D ≤ x → Stab (V k x) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _ x hx; exact tall2 x (by omega)
  | succ k hk ih =>
    intro hk20 x hx
    have hD : D = 204 := D_def
    obtain ⟨N, hN⟩ : ∃ N, 3 * x + 2 - k = N + 1 := ⟨3 * x + 2 - k - 1, by omega⟩
    rw [V_succ, hN, Function.iterate_succ_apply']
    refine ih (by omega) _ ?_
    have h1 := iter_ge (V k) (V_ge k) N (s k)
    have h2 := s_big k hk
    omega

theorem iter_parity (k : ℕ) (hV : ∀ x, k ≤ 3 * x + 2 → V k x % 2 = (x + 1) % 2) (z : ℕ) (hz : k ≤ z) :
    ∀ n, (V k)^[n] z % 2 = (z + n) % 2 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hge := iter_ge (V k) (V_ge k) n z
    rw [hV _ (by omega)]
    omega

/-- Every V_k flips parity, and s_k has the parity of k + 1. -/
theorem parity (k : ℕ) : (∀ x, k ≤ 3 * x + 2 → V k x % 2 = (x + 1) % 2) ∧ s k % 2 = (k + 1) % 2 := by
  induction k with
  | zero => exact ⟨fun x _ => by rw [V_zero]; omega, rfl⟩
  | succ k ih =>
    obtain ⟨hV, hs⟩ := ih
    have hsk := s_ge k
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [V_succ, iter_parity k hV (s k) (by omega)]
      omega
    · rw [s_succ, hV _ (by omega)]
      omega

theorem V_parity (k x : ℕ) (h : k ≤ 3 * x + 2) : V k x % 2 = (x + 1) % 2 := (parity k).1 x h

theorem s_parity (k : ℕ) : s k % 2 = (k + 1) % 2 := (parity k).2

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.v1_mod
#print axioms BeaverStructural.BB7b.stable_val
#print axioms BeaverStructural.BB7b.tall
#print axioms BeaverStructural.BB7b.parity
