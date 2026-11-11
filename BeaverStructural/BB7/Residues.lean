import BeaverStructural.BB7.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.IntervalCases

/-! Residue lemmas for the BB(7) champion's clock.
`powMod b e m = b^e % m` by binary exponentiation with fuel.  For m = 2^a·5^(b+1) and x ≥ a,
2^x ≡ 2^(x mod 4·5^b + 4·5^b·a) (mod m) (`cycle`, Euler's theorem at 5^(b+1)); for m = 2^a and x ≥ a, 2^x ≡ 0.
`towMod h a b = 2↑↑h mod 2^a·5^b` (`towMod_eq`, a ≤ 65536); the tower stabilizes: 2↑↑z ≡ 2↑↑(b+6) (mod 2^a·5^b)
for z ≥ b + 6 (`stable`). -/

namespace BeaverStructural.BB7

open Finset

/-- Binary exponentiation with fuel: `pm m f b e = b^e % m` when e < 2^f. -/
def pm (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % m
  | f + 1, b, e =>
    if e = 0 then 1 % m
    else if e % 2 = 1 then pm m f (b * b % m) (e / 2) * b % m
    else pm m f (b * b % m) (e / 2)

theorem pm_eq (m : ℕ) : ∀ f b e, e < 2 ^ f → pm m f b e = b ^ e % m := by
  intro f
  induction f with
  | zero =>
    intro b e he
    have : e = 0 := by simpa using he
    subst this; simp [pm]
  | succ f ih =>
    intro b e he
    by_cases h0 : e = 0
    · subst h0; simp [pm]
    have hlt : e / 2 < 2 ^ f := by rw [pow_succ] at he; omega
    have hih := ih (b * b % m) (e / 2) hlt
    rw [← Nat.pow_mod] at hih
    have hsplit : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
      rw [← pow_two, ← pow_mul, ← pow_add]; congr 1; omega
    by_cases h1 : e % 2 = 1
    · rw [pm, if_neg h0, if_pos h1, hih, hsplit, h1, pow_one]
      exact Nat.ModEq.mul_right b (Nat.mod_modEq _ m)
    · have h2 : e % 2 = 0 := by omega
      rw [pm, if_neg h0, if_neg h1, hih, hsplit, h2, pow_zero, mul_one]

/-- `powMod b e m = b^e % m`. -/
def powMod (b e m : ℕ) : ℕ := pm m (Nat.log2 e + 1) b e

theorem powMod_eq (b e m : ℕ) : powMod b e m = b ^ e % m := pm_eq m _ b e Nat.lt_log2_self

theorem arrow_one_eq (y : ℕ) : arrow 1 y = 2 ^ y := by
  induction y with
  | zero => rfl
  | succ y ih => rw [arrow_succ_succ, ih]; simp [arrow, pow_succ]; ring

theorem tow_succ (z : ℕ) : arrow 2 (z + 1) = 2 ^ arrow 2 z := by
  rw [arrow_succ_succ, arrow_one_eq]

theorem arrow_gt (k y : ℕ) : y < arrow (k + 1) y := by
  induction k generalizing y with
  | zero => rw [arrow_one_eq]; exact Nat.lt_two_pow_self
  | succ k ih =>
    induction y with
    | zero => rw [arrow_succ_zero]; omega
    | succ y ihy =>
      rw [arrow_succ_succ]
      exact lt_of_le_of_lt (Nat.succ_le_of_lt ihy) (ih _)

theorem tow_le_succ (z : ℕ) : arrow 2 z ≤ arrow 2 (z + 1) := by
  rw [tow_succ]; exact Nat.lt_two_pow_self.le

theorem tow_mono {z z' : ℕ} (h : z ≤ z') : arrow 2 z ≤ arrow 2 z' :=
  monotone_nat_of_le_succ tow_le_succ h

theorem tow_three : arrow 2 3 = 16 := by rw [tow_succ, arrow_two]; norm_num
theorem tow_four : arrow 2 4 = 65536 := by rw [tow_succ, tow_three]; norm_num

theorem tow_ge_of_four {z : ℕ} (h : 4 ≤ z) : 65536 ≤ arrow 2 z := tow_four ▸ tow_mono h

/-- The moduli 2^a·5^b. -/
def md (a b : ℕ) : ℕ := 2 ^ a * 5 ^ b

theorem md_pos (a b : ℕ) : 0 < md a b := by unfold md; positivity

theorem two_pow_cycle_five (b q r : ℕ) : 2 ^ (md 2 b * q + r) ≡ 2 ^ r [MOD 5 ^ (b + 1)] := by
  have hcop : Nat.Coprime 2 (5 ^ (b + 1)) := Nat.Coprime.pow_right _ (by norm_num)
  have ht := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime_pow_succ Nat.prime_five] at ht
  have hL : md 2 b = 5 ^ b * (5 - 1) := by unfold md; ring
  have hx : 2 ^ (md 2 b * q + r) = (2 ^ (5 ^ b * (5 - 1))) ^ q * 2 ^ r := by
    rw [hL, pow_add, pow_mul]
  rw [hx]
  calc (2 ^ (5 ^ b * (5 - 1))) ^ q * 2 ^ r ≡ 1 ^ q * 2 ^ r [MOD 5 ^ (b + 1)] := (ht.pow q).mul_right _
    _ = 2 ^ r := by simp

/-- For m = 2^a·5^(b+1) and x ≥ a: 2^x ≡ 2^(x mod 4·5^b + 4·5^b·a). -/
theorem cycle (a b x : ℕ) (hx : a ≤ x) :
    2 ^ x % md a (b + 1) = 2 ^ (x % md 2 b + md 2 b * a) % md a (b + 1) := by
  have hL : 1 ≤ md 2 b := md_pos 2 b
  have hcop : Nat.Coprime (2 ^ a) (5 ^ (b + 1)) := Nat.Coprime.pow _ _ (by norm_num)
  have h5 : 2 ^ x ≡ 2 ^ (x % md 2 b + md 2 b * a) [MOD 5 ^ (b + 1)] := by
    have e1 : 2 ^ x ≡ 2 ^ (x % md 2 b) [MOD 5 ^ (b + 1)] := by
      have := two_pow_cycle_five b (x / md 2 b) (x % md 2 b)
      rwa [Nat.div_add_mod] at this
    have e2 : 2 ^ (x % md 2 b + md 2 b * a) ≡ 2 ^ (x % md 2 b) [MOD 5 ^ (b + 1)] := by
      rw [Nat.add_comm (x % md 2 b)]; exact two_pow_cycle_five b a _
    exact e1.trans e2.symm
  have h2 : 2 ^ x ≡ 2 ^ (x % md 2 b + md 2 b * a) [MOD 2 ^ a] := by
    have d1 : 2 ^ a ∣ 2 ^ x := pow_dvd_pow 2 hx
    have d2 : 2 ^ a ∣ 2 ^ (x % md 2 b + md 2 b * a) :=
      pow_dvd_pow 2 (le_trans (Nat.le_mul_of_pos_left a hL) (Nat.le_add_left _ _))
    exact (Nat.modEq_zero_iff_dvd.2 d1).trans (Nat.modEq_zero_iff_dvd.2 d2).symm
  exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h2, h5⟩

theorem cycle0 (a x : ℕ) (hx : a ≤ x) : 2 ^ x % md a 0 = 0 := by
  unfold md; rw [pow_zero, mul_one]
  exact Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 hx)

/-- 2↑↑h for h < 4. -/
def smallTow : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 16
  | _ => 65536

theorem smallTow_eq (h : ℕ) (hh : h < 4) : smallTow h = arrow 2 h := by
  interval_cases h
  · rfl
  · rw [arrow_one]; rfl
  · rw [arrow_two]; rfl
  · rw [tow_three]; rfl

/-- `towMod h a b = 2↑↑h mod 2^a·5^b` for a ≤ 65536. -/
def towMod : ℕ → ℕ → ℕ → ℕ
  | 0, a, b => 1 % md a b
  | h + 1, a, 0 => if h < 4 then 2 ^ smallTow h % md a 0 else 0
  | h + 1, a, b + 1 =>
    if h < 4 then powMod 2 (smallTow h) (md a (b + 1))
    else powMod 2 (towMod h 2 b + md 2 b * a) (md a (b + 1))

theorem towMod_eq : ∀ h a b, a ≤ 65536 → towMod h a b = arrow 2 h % md a b := by
  intro h
  induction h with
  | zero => intro a b _; rfl
  | succ h ih =>
    intro a b ha
    cases b with
    | zero =>
      by_cases hh : h < 4
      · simp only [towMod, hh, if_true, tow_succ, smallTow_eq h hh]
      · simp only [towMod, hh, if_false, tow_succ]
        exact (cycle0 a _ (le_trans ha (tow_ge_of_four (by omega)))).symm
    | succ b =>
      by_cases hh : h < 4
      · simp only [towMod, hh, if_true, tow_succ, smallTow_eq h hh, powMod_eq]
      · simp only [towMod, hh, if_false, tow_succ, powMod_eq, ih 2 b (by norm_num)]
        exact (cycle a b _ (le_trans ha (tow_ge_of_four (by omega)))).symm

/-- The tower stabilizes mod 2^a·5^b from height b + 6. -/
theorem stable : ∀ b a z, a ≤ 65536 → b + 6 ≤ z → arrow 2 z % md a b = arrow 2 (b + 6) % md a b := by
  intro b
  induction b with
  | zero =>
    intro a z ha hz
    obtain ⟨z', rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
    rw [tow_succ, show 0 + 6 = 5 + 1 by rfl, tow_succ,
      cycle0 a _ (le_trans ha (tow_ge_of_four (by omega))),
      cycle0 a _ (le_trans ha (tow_ge_of_four (by omega)))]
  | succ b ih =>
    intro a z ha hz
    obtain ⟨z', rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
    rw [tow_succ, show b + 1 + 6 = (b + 6) + 1 by ring, tow_succ,
      cycle a b _ (le_trans ha (tow_ge_of_four (by omega))),
      cycle a b _ (le_trans ha (tow_ge_of_four (by omega))),
      ih 2 z' (by norm_num) (by omega)]

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.powMod_eq
#print axioms BeaverStructural.BB7.cycle
#print axioms BeaverStructural.BB7.towMod_eq
#print axioms BeaverStructural.BB7.stable

