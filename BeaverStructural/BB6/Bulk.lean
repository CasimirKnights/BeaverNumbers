import BeaverStructural.BB6.Arithmetic
import Mathlib.Algebra.BigOperators.Intervals

namespace BeaverStructural.BB6

def phaseMode (j : ℕ) : ℕ := 2-j%3
def phaseWidth (j b : ℕ) : ℕ := towerSum (j+1) b +5*(j/3)+2*(j%3)

theorem phaseMode_lt_three (j : ℕ) : phaseMode j < 3 := by unfold phaseMode; omega

theorem phaseMode_succ (j : ℕ) : phaseMode (j+1) = (phaseMode j+2)%3 := by
  unfold phaseMode
  omega

theorem phaseWidth_zero (b : ℕ) : phaseWidth 0 b = b := by
  simp [phaseWidth, towerSum]

theorem phaseWidth_succ (j b : ℕ) :
    phaseWidth (j+1) b = phaseWidth j b +tower (j+1) b +
      (if phaseMode j=0 then 1 else 2) := by
  unfold phaseWidth phaseMode
  rw [towerSum_succ (j+1)]
  split_ifs <;> omega

theorem phaseWidth_mode_cost (j b : ℕ) :
    12*phaseWidth j b+4*phaseMode j+63 = 12*towerSum (j+1) b+20*j+71 := by
  unfold phaseWidth phaseMode
  omega

theorem tower_monotone (b : ℕ) : Monotone (fun h => tower h b) :=
  monotone_nat_of_le_succ (fun h => tower_step_mono h b)

theorem towerWeightedSum_succ (n b : ℕ) :
    towerWeightedSum (n+1) b = towerWeightedSum n b + towerSum (n+1) b := by
  unfold towerWeightedSum towerSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  have hsum : (∑ i ∈ Finset.range n, (n+1-i)*tower i b) =
      (∑ i ∈ Finset.range n, (n-i)*tower i b) + ∑ i ∈ Finset.range n, tower i b := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    rw [show n+1-i = (n-i)+1 by omega, Nat.add_mul]
    simp
  rw [hsum]
  simp
  omega

theorem sum_tower_prefixes (n b : ℕ) :
    (∑ j ∈ Finset.range n, towerSum (j+1) b) = towerWeightedSum n b := by
  induction n with
  | zero => simp [towerWeightedSum]
  | succ n ih => rw [Finset.sum_range_succ, ih, towerWeightedSum_succ]

theorem sum_tower_rises (n b : ℕ) :
    (∑ j ∈ Finset.range n, (tower (j+2) b-tower (j+1) b)) =
      tower (n+1) b-tower 1 b := by
  exact Finset.sum_range_tsub (fun i j hij => tower_monotone b (by omega : i+1 ≤ j+1)) n

theorem sum_mode_costs (n : ℕ) :
    (∑ j ∈ Finset.range n, (20*j+71)) = 10*n^2+61*n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem reverse_binary_carry_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, padicValNat 2 (n-j)) = binaryCarry n := by
  rw [← binary_carry_sum]
  rw [← Finset.sum_range_reflect (fun j => padicValNat 2 (j+1)) n]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  have := Finset.mem_range.mp hj
  omega

theorem binaryCarry_succ (n : ℕ) :
    binaryCarry (n+1) = binaryCarry n + padicValNat 2 (n+1) := by
  rw [← binary_carry_sum (n+1), Finset.sum_range_succ, binary_carry_sum]

def innerCost (n b : ℕ) : ℕ := 6*n^2+(12*b+42)*n+12*binaryCarry n

theorem innerCost_zero (b : ℕ) : innerCost 0 b = 0 := by
  simp [innerCost, binaryCarry]

theorem innerCost_succ (n b : ℕ) :
    innerCost (n+1) b = 12*padicValNat 2 (n+1)+12*b+48+innerCost n (b+1) := by
  simp only [innerCost, binaryCarry_succ]
  ring

theorem innerCost_counted_polynomial (n b : ℕ) :
    (innerCost n b : ℤ) = 6*(n:ℤ)^2+(12*b+54)*n-12*binaryPopulation n := by
  have h := population_le n
  simp only [innerCost, binaryCarry, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_sub h]
  ring

theorem binaryPopulation_all_ones (b : ℕ) : binaryPopulation (2^b-1) = b := by
  induction b with
  | zero => simp [binaryPopulation]
  | succ b ih =>
    have hp : 0 < (2:ℕ)^b := by positivity
    have heq : (2:ℕ)^(b+1)-1 = 1+2*(2^b-1) := by rw [pow_succ]; omega
    unfold binaryPopulation at ih ⊢
    rw [heq, Nat.digits_add 2 (by decide) 1 (2^b-1) (by decide) (Or.inl (by decide))]
    simp only [List.sum_cons, ih]
    omega

theorem innerCost_all_ones (b : ℕ) :
    (innerCost (2^b-1) 0 : ℤ) =
      6*((2:ℤ)^b-1)^2+54*((2:ℤ)^b-1)-12*b := by
  have hp : 1 ≤ (2:ℕ)^b := by have := self_lt_two_pow b; omega
  rw [innerCost_counted_polynomial, binaryPopulation_all_ones]
  simp only [Nat.cast_sub hp, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- Reset counters have one zero separating two exact runs of one-bits. -/
theorem binaryPopulation_reset (L a : ℕ) :
    binaryPopulation ((2^(L+2)-1)*2^a-1)=L+a+1 := by
  induction a with
  | zero =>
    have hp : 1<(2:ℕ)^(L+1) := by
      calc 1 < L+1+1 := by omega
           _ ≤ 2^(L+1) := self_lt_two_pow (L+1)
    have heq : ((2:ℕ)^(L+2)-1)*2^0-1=2*(2^(L+1)-1) := by
      rw [show L+2=(L+1)+1 by omega, pow_succ]
      omega
    rw [heq]
    unfold binaryPopulation
    rw [Nat.digits_base_mul (by decide) (by omega)]
    change 0+binaryPopulation (2^(L+1)-1)=L+0+1
    rw [binaryPopulation_all_ones]
    omega
  | succ a ih =>
    have hp : 0<(2^ (L+2)-1)*(2:ℕ)^a := by
      have hL : 0 < (2:ℕ)^(L+2)-1 := by have := self_lt_two_pow (L+2); omega
      exact Nat.mul_pos hL (by positivity)
    have heq : ((2:ℕ)^(L+2)-1)*2^(a+1)-1 =
        1+2*((2^(L+2)-1)*2^a-1) := by
      rw [pow_succ 2 a, ← Nat.mul_assoc]
      omega
    unfold binaryPopulation at ih ⊢
    rw [heq, Nat.digits_add 2 (by decide) 1 _ (by decide) (Or.inl (by decide))]
    simp only [List.sum_cons, ih]
    omega

theorem binaryCarry_reset (L a : ℕ) :
    binaryCarry ((2^(L+2)-1)*2^a-1)=2^(L+a+2)-2^a-(L+a+2) := by
  unfold binaryCarry
  rw [binaryPopulation_reset]
  have hp : 0<(2:ℕ)^(L+2) := by positivity
  have heq : (2:ℕ)^(L+a+2)=2^(L+2)*2^a := by
    rw [← pow_add]
    congr 1
    omega
  rw [heq, Nat.sub_mul]
  omega

/-- The counted cost of positive outer phase j, rearranged so subtraction
only appears in the nonnegative tower rise. No instructions are omitted. -/
def phaseCost (n b j : ℕ) : ℕ :=
  6*(tower (j+2) b)^2 +45*tower (j+2) b +
  9*(tower (j+2) b-tower (j+1) b) +12*towerSum (j+1) b +
  (20*j+71) +12*padicValNat 2 (n-j)

theorem phaseCost_counted_polynomial (n b j : ℕ) :
    (phaseCost n b j : ℤ) =
      6*(tower (j+2) b : ℤ)^2 +54*tower (j+2) b -9*tower (j+1) b +
      12*towerSum (j+1) b +20*j+71+12*padicValNat 2 (n-j) := by
  have hle : tower (j+1) b ≤ tower (j+2) b := tower_step_mono (j+1) b
  simp only [phaseCost, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_sub hle]
  ring

/-- Exact finite sum identity for all n,b. The separate source theorem must
prove each phaseCost is the instruction count of its original tape rewrite. -/
theorem bulkCost_eq_sum_phaseCost (n b : ℕ) :
    bulkCost n b = ∑ j ∈ Finset.range n, phaseCost n b j := by
  have hm := sum_mode_costs n
  rw [Finset.sum_add_distrib] at hm
  simp only [phaseCost, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_tower_rises, sum_tower_prefixes, reverse_binary_carry_sum]
  have h1 : (∑ j ∈ Finset.range n, tower (j+2) b) = towerSum n (tower 2 b) := by
    simp only [towerSum, tower_add]
  have h2 : (∑ j ∈ Finset.range n, (tower (j+2) b)^2) = towerSquareSum n (tower 2 b) := by
    simp only [towerSquareSum, tower_add]
  rw [h1, h2]
  unfold bulkCost
  omega

end BeaverStructural.BB6
