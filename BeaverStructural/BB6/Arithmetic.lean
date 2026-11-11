import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-! Exact natural arithmetic used by the original BB6 counter construction.
These definitions do not assert that a machine reaches their values. -/
namespace BeaverStructural.BB6

def tower : ℕ → ℕ → ℕ
  | 0, b => b
  | h + 1, b => 2 ^ tower h b - 1

@[simp] theorem tower_zero (b : ℕ) : tower 0 b = b := rfl
@[simp] theorem tower_succ (h b : ℕ) : tower (h+1) b = 2 ^ tower h b - 1 := rfl

theorem self_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem tower_step_mono (h b : ℕ) : tower h b ≤ tower (h+1) b := by
  rw [tower_succ]
  have := self_lt_two_pow (tower h b)
  omega

theorem le_tower (h b : ℕ) : b ≤ tower h b := by
  induction h with
  | zero => rfl
  | succ h ih => exact ih.trans (tower_step_mono h b)

theorem tower_add (h k b : ℕ) : tower (h+k) b = tower h (tower k b) := by
  induction h with
  | zero => simp
  | succ h ih => simpa [Nat.succ_add, tower_succ] using congrArg (fun x => 2^x-1) ih

theorem pow_two_mod_two (n : ℕ) (hn : 0 < n) : 2 ^ n % 2 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp [pow_succ, Nat.mul_mod]

theorem tower_succ_odd (h b : ℕ) (hb : 0 < b) : tower (h+1) b % 2 = 1 := by
  have hp := pow_two_mod_two (tower h b) (lt_of_lt_of_le hb (le_tower h b))
  have hpos : 0 < 2 ^ tower h b := by positivity
  rw [tower_succ]
  omega

theorem pow_two_mod_three (n : ℕ) :
    2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs <;> omega

def towerSum (count base : ℕ) : ℕ := ∑ i ∈ Finset.range count, tower i base
def towerSquareSum (count base : ℕ) : ℕ := ∑ i ∈ Finset.range count, (tower i base)^2
def towerWeightedSum (count base : ℕ) : ℕ :=
  ∑ i ∈ Finset.range count, (count-i) * tower i base

@[simp] theorem towerSum_zero (b : ℕ) : towerSum 0 b = 0 := by simp [towerSum]
@[simp] theorem towerSum_succ (n b : ℕ) : towerSum (n+1) b = towerSum n b + tower n b := by
  simp [towerSum, Finset.sum_range_succ]

theorem towerSum_parity (n b : ℕ) (hb : 0 < b) :
    towerSum (n+1) b % 2 = (b+n) % 2 := by
  induction n with
  | zero => simp [towerSum]
  | succ n ih =>
    rw [towerSum_succ, Nat.add_mod, tower_succ_odd n b hb, ih]
    omega

def binaryPopulation (n : ℕ) : ℕ := (Nat.digits 2 n).sum
def binaryCarry (n : ℕ) : ℕ := n - binaryPopulation n

def bulkCost (n b : ℕ) : ℕ :=
  6*towerSquareSum n (tower 2 b) +45*towerSum n (tower 2 b) +
  9*(tower (n+1) b-tower 1 b) +12*towerWeightedSum n b +
  10*n^2+61*n+12*binaryCarry n

theorem population_le (n : ℕ) : binaryPopulation n ≤ n := Nat.digit_sum_le 2 n

theorem binaryCarry_eq_factorial_valuation (n : ℕ) :
    binaryCarry n = padicValNat 2 n.factorial := by
  simpa [binaryCarry, binaryPopulation] using (sub_one_mul_padicValNat_factorial (p := 2) n).symm

theorem binary_carry_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, padicValNat 2 (j+1)) = binaryCarry n := by
  rw [binaryCarry_eq_factorial_valuation]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.factorial_succ,
      padicValNat.mul (by omega : n+1 ≠ 0) (Nat.factorial_ne_zero n), ← ih]
    omega

end BeaverStructural.BB6
