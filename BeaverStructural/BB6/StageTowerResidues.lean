import BeaverStructural.BB6.TowerResidueSums
import BeaverStructural.BB6.DecimalResidues

/-! Source-specific tower residues for the two actual reset stages.
The second stage's complete residue tail is derived from the proved first-stage
count, not supplied as an unproved stability hypothesis. -/
namespace BeaverStructural.BB6.TowerModulus

attribute [local irreducible] tower towerSum towerSquareSum towerWeightedSum stage1 stage2

theorem stage1_tower_residue {m : ℕ} (C : TowerModulus m) (j : ℕ) :
    tower j stage1.base%m=C.residue (j+8) := by
  rw [tower_stage1]
  exact C.residue_correct _

theorem stage1_tower_steady {m : ℕ} (C : TowerModulus m) (j : ℕ)
    (hj : C.depth+2≤j+8) : tower j stage1.base%m=C.steady := by
  rw [tower_stage1]
  exact C.steady_correct _ hj

theorem stage1_sumCode {m : ℕ} (C : TowerModulus m) (offset n : ℕ)
    (hn : C.depth+2≤n) :
    towerSum n (tower offset stage1.base)%m=C.sumCode (offset+8) (n%m) := by
  unfold towerSum
  simp_rw [← tower_add, tower_stage1]
  have he (i : ℕ) : i+offset+8=(offset+8)+i := by omega
  simp_rw [he]
  exact C.sumCode_correct (offset+8) n hn

theorem stage1_powerCode {m : ℕ} (C : TowerModulus m) (offset n power : ℕ)
    (hn : C.depth+2≤n) :
    (∑ i ∈ Finset.range n, (tower i (tower offset stage1.base))^power)%m=
      C.powerCode (offset+8) (n%m) power := by
  simp_rw [← tower_add, tower_stage1]
  have he (i : ℕ) : i+offset+8=(offset+8)+i := by omega
  simp_rw [he]
  exact C.powerCode_correct (offset+8) n power hn

theorem stage1_squareCode {m : ℕ} (C : TowerModulus m) (n : ℕ)
    (hn : C.depth+2≤n) :
    towerSquareSum n (tower 2 stage1.base)%m=C.powerCode 10 (n%m) 2 := by
  unfold towerSquareSum
  exact C.stage1_powerCode 2 n 2 hn

theorem stage1_weightedCode {m : ℕ} (C : TowerModulus m) (n : ℕ)
    (hn : C.depth+2≤n) :
    (2*towerWeightedSum n stage1.base)%m=C.weightedCode 8 (n%m) := by
  unfold towerWeightedSum
  simp_rw [tower_stage1]
  have he (i : ℕ) : i+8=8+i := by omega
  simp_rw [he]
  exact C.weightedCode_correct 8 n hn

theorem actual_stage1_count_lower : 847≤stage1.count := by
  have h := stage1_count_mod_thousand
  have hm := Nat.mod_le stage1.count 1000
  omega

/-- Every tower index of the actual second-stage base is beyond the certified
stabilization depth, including its zero-th tower index. -/
theorem stage2_tower_steady {m : ℕ} (C : TowerModulus m)
    (hd : C.depth+2≤856) (j : ℕ) : tower j stage2.base%m=C.steady := by
  rewrite [stage2, tower_reset_base, tower_stage1]
  exact C.steady_correct _ (by have := actual_stage1_count_lower; omega)

theorem steady_mod {m : ℕ} (C : TowerModulus m) : C.steady%m=C.steady := by
  rw [← C.steady_correct (C.depth+2) (by omega), Nat.mod_mod]

theorem stage2_tower_shift_mod {m : ℕ} (C : TowerModulus m)
    (hd : C.depth+2≤856) (offset j : ℕ) :
    tower j (tower offset stage2.base)%m=C.steady%m := by
  rw [← tower_add, C.stage2_tower_steady hd, C.steady_mod]

theorem stage2_sum_residue {m : ℕ} (C : TowerModulus m)
    (hd : C.depth+2≤856) (offset n : ℕ) :
    towerSum n (tower offset stage2.base)%m=((n%m)*C.steady)%m := by
  rw [towerSum_mod_constant n (tower offset stage2.base) m C.steady
    (C.stage2_tower_shift_mod hd offset)]
  simp only [Nat.mul_mod, Nat.mod_mod]

theorem stage2_square_residue {m : ℕ} (C : TowerModulus m)
    (hd : C.depth+2≤856) (offset n : ℕ) :
    towerSquareSum n (tower offset stage2.base)%m=((n%m)*C.steady^2)%m := by
  rw [towerSquareSum_mod_constant n (tower offset stage2.base) m C.steady
    (C.stage2_tower_shift_mod hd offset)]
  simp only [Nat.mul_mod, Nat.mod_mod]

theorem stage2_weighted_residue {m : ℕ} (C : TowerModulus m)
    (hd : C.depth+2≤856) (n : ℕ) :
    (2*towerWeightedSum n stage2.base)%m=((n%m)*((n%m)+1)*C.steady)%m := by
  have ht (j : ℕ) : tower j stage2.base%m=C.steady%m := by
    rw [C.stage2_tower_steady hd, C.steady_mod]
  rw [towerWeightedSum_twice_mod_constant n stage2.base m C.steady ht]
  simp only [Nat.mul_mod, Nat.add_mod, Nat.mod_mod]

end BeaverStructural.BB6.TowerModulus
