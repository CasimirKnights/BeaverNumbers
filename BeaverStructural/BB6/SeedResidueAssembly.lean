import BeaverStructural.BB6.ModularClockAssembly
import BeaverStructural.BB6.TowerModuli
import Mathlib.Algebra.BigOperators.ModEq

/-! The original seven-count seed's finite sums assembled from a certified
modulus tree. No astronomical tower is evaluated or replaced by an answer. -/
namespace BeaverStructural.BB6.SeedResidue
open ModularClock
set_option compiler.extract_closed false
attribute [local irreducible] tower towerSum towerSquareSum towerWeightedSum
  bulkCost resetCost exhaustedWidth exhaustedRight

variable {m : ℕ}

theorem modulus_pos (C : TowerModulus m) : 0<m := by
  cases C with
  | one => omega
  | step child hm hp period => exact hm

theorem residue_modEq (C : TowerModulus m) (h : ℕ) : tower h 6 ≡ C.residue h [MOD m] := by
  change tower h 6%m=C.residue h%m
  rw [← C.residue_correct h,Nat.mod_mod]

def seedSquareValue (C : TowerModulus m) : ℕ :=
  (∑ i ∈ Finset.range 7, (C.residue (i+2))^2)%m

def seedLinearValue (C : TowerModulus m) : ℕ :=
  (∑ i ∈ Finset.range 7, C.residue (i+2))%m

def seedTwiceWeightedValue (C : TowerModulus m) : ℕ :=
  (2*∑ i ∈ Finset.range 7, (7-i)*C.residue i)%m

def seedWidthValue (C : TowerModulus m) : ℕ :=
  ((∑ i ∈ Finset.range 8, C.residue i)+12)%m

def seedBulkCode (C : TowerModulus m) : ℕ :=
  bulkCode m (7%m) (seedSquareValue C) (seedLinearValue C)
    (C.residue 8) (C.residue 1) (seedTwiceWeightedValue C) (4%m)

def seedResetCode (C : TowerModulus m) : ℕ :=
  resetCode m (3%m) (seedWidthValue C) (C.residue 8) (C.residue 9)

theorem square_sum_mod (m n b k : ℕ) (r : ℕ→ℕ)
    (hr : ∀ i, tower (i+k) b ≡ r i [MOD m]) :
    towerSquareSum n (tower k b)%m=(∑ i ∈ Finset.range n, (r i)^2)%m := by
  unfold towerSquareSum
  apply Nat.ModEq.sum
  intro i _
  rewrite [← tower_add]
  exact (hr i).pow 2

theorem linear_sum_mod (m n b k : ℕ) (r : ℕ→ℕ)
    (hr : ∀ i, tower (i+k) b ≡ r i [MOD m]) :
    towerSum n (tower k b)%m=(∑ i ∈ Finset.range n, r i)%m := by
  unfold towerSum
  apply Nat.ModEq.sum
  intro i _
  rewrite [← tower_add]
  exact hr i

theorem weighted_sum_mod (m n b : ℕ) (r : ℕ→ℕ)
    (hr : ∀ i, tower i b ≡ r i [MOD m]) :
    (2*towerWeightedSum n b)%m=(2*∑ i ∈ Finset.range n, (n-i)*r i)%m := by
  unfold towerWeightedSum
  apply Nat.ModEq.mul_left 2
  apply Nat.ModEq.sum
  intro i _
  exact (hr i).mul_left (n-i)

theorem seed_width_mod (m b : ℕ) (r : ℕ→ℕ)
    (hr : ∀ i, tower i b ≡ r i [MOD m]) :
    exhaustedWidth ⟨3,7,b⟩%m=((∑ i ∈ Finset.range 8, r i)+12)%m := by
  rewrite [width_seed_shape b]
  unfold towerSum
  apply Nat.ModEq.add_right 12
  apply Nat.ModEq.sum
  intro i _
  exact hr i

theorem seedSquareValue_correct (C : TowerModulus m) :
    towerSquareSum 7 (tower 2 6)%m=seedSquareValue C :=
  square_sum_mod m 7 6 2 (fun i => C.residue (i+2)) (fun i => residue_modEq C (i+2))

theorem seedLinearValue_correct (C : TowerModulus m) :
    towerSum 7 (tower 2 6)%m=seedLinearValue C :=
  linear_sum_mod m 7 6 2 (fun i => C.residue (i+2)) (fun i => residue_modEq C (i+2))

theorem seedTwiceWeightedValue_correct (C : TowerModulus m) :
    (2*towerWeightedSum 7 6)%m=seedTwiceWeightedValue C :=
  weighted_sum_mod m 7 6 C.residue (residue_modEq C)

theorem seedWidthValue_correct (C : TowerModulus m) :
    exhaustedWidth seed%m=seedWidthValue C := seed_width_mod m 6 C.residue (residue_modEq C)

theorem seedBulkCode_correct (C : TowerModulus m) :
    bulkCost seed.count seed.base%m=seedBulkCode C := by
  change bulkCost 7 6%m=_
  exact bulkCode_correct m 7 6 (7%m) (seedSquareValue C) (seedLinearValue C)
    (C.residue 8) (C.residue 1) (seedTwiceWeightedValue C) (4%m)
    (modulus_pos C) rfl (seedSquareValue_correct C) (seedLinearValue_correct C)
    (C.residue_correct 8) (C.residue_correct 1) (seedTwiceWeightedValue_correct C)
    (by rw [show binaryCarry 7=4 by decide])

theorem seedResetCode_correct (C : TowerModulus m) :
    resetCost seed.length (exhaustedWidth seed) (exhaustedRight seed)%m=seedResetCode C := by
  have hb : exhaustedRight seed=tower 8 6 := by unfold exhaustedRight seed; rfl
  have hs : 2^exhaustedRight seed-1=tower 9 6 := by rw [hb]; exact (tower_succ 8 6).symm
  exact resetCode_correct m seed.length (exhaustedWidth seed) (exhaustedRight seed)
    (3%m) (seedWidthValue C) (C.residue 8) (C.residue 9) (modulus_pos C) rfl
    (seedWidthValue_correct C) (by rw [hb]; exact C.residue_correct 8)
    (by rw [hs]; exact C.residue_correct 9)

end BeaverStructural.BB6.SeedResidue
