import BeaverStructural.BB6.Bulk

set_option compiler.extract_closed false

namespace BeaverStructural.BB6

attribute [local irreducible] tower towerSum towerSquareSum towerWeightedSum

structure Counter where
  length : ℕ
  count : ℕ
  base : ℕ

def exhaustedWidth (C : Counter) : ℕ :=
  towerSum (C.count+1) C.base + 5*(C.count/3) +
    (if C.count%3 = 1 then 2 else 4)

def exhaustedRight (C : Counter) : ℕ := tower (C.count+1) C.base

def resetCounter (C : Counter) : Counter :=
  ⟨C.length + exhaustedWidth C + 2,
   (2^(C.length+2)-1)*2^exhaustedWidth C-1,
   exhaustedRight C⟩

attribute [local irreducible] exhaustedWidth exhaustedRight

theorem resetCounter_length (C : Counter) :
    (resetCounter C).length = C.length+exhaustedWidth C+2 := rfl
theorem resetCounter_count (C : Counter) :
    (resetCounter C).count = (2^(C.length+2)-1)*2^exhaustedWidth C-1 := rfl
theorem resetCounter_base (C : Counter) :
    (resetCounter C).base = exhaustedRight C := rfl
attribute [local irreducible] resetCounter

/-- Nonnegative rearrangement of the original counted reset polynomial. -/
def resetCost (L a b : ℕ) : ℕ :=
  let s := 2^b-1
  6*s^2+45*s+9*(s-b)+12*L+12*a+97

def haltCost (L a : ℕ) : ℕ := 12*L+12*a+60

def seed : Counter := ⟨3,7,6⟩
noncomputable def stage1 : Counter := resetCounter seed
noncomputable def stage2 : Counter := resetCounter stage1

attribute [local irreducible] stage1 stage2

/-- Explicit arithmetic expression. Its equality to the original first-hit
clock is proved separately from counted source execution. -/
def clockFor (C0 C1 C2 : Counter) : ℕ :=
  27965 + bulkCost C0.count C0.base +
  resetCost C0.length (exhaustedWidth C0) (exhaustedRight C0) +
  bulkCost C1.count C1.base +
  resetCost C1.length (exhaustedWidth C1) (exhaustedRight C1) +
  bulkCost C2.count C2.base + haltCost C2.length (exhaustedWidth C2)

noncomputable irreducible_def exactN : ℕ := clockFor seed stage1 stage2

theorem resetCost_counted_polynomial (L a b : ℕ) :
    (resetCost L a b : ℤ) =
      6*((2:ℤ)^b-1)^2+54*((2:ℤ)^b-1)+12*L+12*a-9*b+97 := by
  have hp : 1 ≤ (2:ℕ)^b := by have := self_lt_two_pow b; omega
  have hb : b ≤ (2:ℕ)^b-1 := by have := self_lt_two_pow b; omega
  simp only [resetCost, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_sub hp, Nat.cast_sub hb]
  ring

theorem seed_residue : seed.count % 3 = 1 := by decide

theorem odd_add_two_even (a b c : ℕ) (ha : a%2=1) (hb : b%2=0)
    (hc : c%2=0) : (a+b+c)%2=1 := by omega

theorem three_add_odd_add_two (a : ℕ) (ha : a%2=1) : (3+a+2)%2=0 := by omega

theorem odd_add_odd_add_two (L a : ℕ) (hL : L%2=1) (ha : a%2=1) :
    (L+a+2)%2=0 := by omega

theorem exhaustedWidth_parity (C : Counter) (hb : 0 < C.base) :
    exhaustedWidth C % 2 =
      (C.base+C.count+5*(C.count/3)+(if C.count%3=1 then 2 else 4))%2 := by
  simp only [exhaustedWidth, Nat.add_mod, Nat.mod_mod, towerSum_parity C.count C.base hb]

theorem exhaustedWidth_eq_phaseWidth (C : Counter)
    (hr : C.count%3=1 ∨ C.count%3=2) : exhaustedWidth C = phaseWidth C.count C.base := by
  unfold exhaustedWidth phaseWidth
  rcases hr with hr | hr
  · rw [hr]; simp
  · rw [hr]; simp

theorem phaseMode_of_one (n : ℕ) (hn : n%3=1) : phaseMode n=1 := by
  unfold phaseMode
  omega

theorem phaseMode_of_two (n : ℕ) (hn : n%3=2) : phaseMode n=0 := by
  unfold phaseMode
  omega

theorem seed_width_odd : exhaustedWidth seed % 2 = 1 := by
  exact (exhaustedWidth_parity seed (show 0<6 by decide)).trans
    (show (6+7+5*(7/3)+(if 7%3=1 then 2 else 4))%2=1 by decide)

theorem stage1_length_even : stage1.length % 2 = 0 := by
  rewrite [stage1, resetCounter_length]
  exact odd_add_odd_add_two seed.length (exhaustedWidth seed) (by decide) seed_width_odd

theorem first_reset_residue (a : ℕ) (ha : a%2=1) : (31*2^a-1)%3=1 := by
  have hp := pow_two_mod_three a
  have hpos : 0 < 2^a := by positivity
  have hmul : (31*2^a)%3=2 := by
    rw [Nat.mul_mod, hp]
    rw [if_neg (by omega)]
  omega

theorem even_length_reset_residue (L a : ℕ) (hl : L%2=0) :
    ((2^(L+2)-1)*2^a-1)%3=2 := by
  have hp := pow_two_mod_three (L+2)
  have hpow : 2^(L+2)%3=1 := by rw [hp, if_pos (by omega)]
  have hpos : 0 < 2^(L+2) := by positivity
  have hfactor : (2^(L+2)-1)%3=0 := by omega
  have hmul : ((2^(L+2)-1)*2^a)%3=0 := by
    simp [Nat.mul_mod, hfactor]
  have hbig := self_lt_two_pow (L+2)
  have htwo : 0 < 2^a := by positivity
  have hprod : 0 < (2^(L+2)-1)*2^a := Nat.mul_pos (by omega) htwo
  omega

theorem odd_length_reset_residue (L a : ℕ) (hl : L%2=1) (ha : a%2=1) :
    ((2^(L+2)-1)*2^a-1)%3=1 := by
  have hp := pow_two_mod_three (L+2)
  have hpow : 2^(L+2)%3=2 := by rw [hp, if_neg (by omega)]
  have hpos : 0 < 2^(L+2) := by positivity
  have hfactor : (2^(L+2)-1)%3=1 := by omega
  have hpa : 2^a%3=2 := by rw [pow_two_mod_three, if_neg (by omega)]
  have hmul : ((2^(L+2)-1)*2^a)%3=2 := by rw [Nat.mul_mod, hfactor, hpa]
  have hbig := self_lt_two_pow (L+2)
  have htwo : 0 < 2^a := by positivity
  have hprod : 0 < (2^(L+2)-1)*2^a := Nat.mul_pos (by omega) htwo
  omega

theorem stage1_residue : stage1.count % 3 = 1 := by
  rewrite [stage1, resetCounter_count]
  exact odd_length_reset_residue seed.length (exhaustedWidth seed) (by decide) seed_width_odd

theorem stage2_residue : stage2.count % 3 = 2 := by
  rewrite [stage2, resetCounter_count]
  exact even_length_reset_residue _ _ stage1_length_even

theorem actual_branch_sequence :
    seed.count%3=1 ∧ stage1.count%3=1 ∧ stage2.count%3=2 :=
  ⟨seed_residue, stage1_residue, stage2_residue⟩

theorem reset_count_bound (L a : ℕ) :
    (2^(L+2)-1)*2^a-1 < 2^(L+a+2) := by
  have hp : 0 < (2:ℕ)^(L+2) := by positivity
  have hq : 0 < (2:ℕ)^a := by positivity
  have hm := Nat.mul_lt_mul_of_pos_right (show 2^(L+2)-1 < 2^(L+2) by omega) hq
  have heq : (2:ℕ)^(L+a+2) = 2^(L+2)*2^a := by
    rw [← pow_add]
    congr 1
    omega
  rw [heq]
  exact lt_of_le_of_lt (Nat.sub_le _ _) hm

theorem resetCounter_bound (C : Counter) :
    (resetCounter C).count < 2^(resetCounter C).length := by
  rewrite [resetCounter_count, resetCounter_length]
  exact reset_count_bound C.length (exhaustedWidth C)

theorem resetCounter_base_ge (C : Counter) : C.base ≤ (resetCounter C).base := by
  rewrite [resetCounter_base, exhaustedRight]
  exact le_tower _ _

theorem seed_count_bound : seed.count < 2^seed.length := by decide
theorem seed_base_ge_two : 2 ≤ seed.base := by decide

theorem stage1_count_bound : stage1.count < 2^stage1.length := by
  rewrite [stage1]
  exact resetCounter_bound seed

theorem stage2_count_bound : stage2.count < 2^stage2.length := by
  rewrite [stage2]
  exact resetCounter_bound stage1

theorem stage1_base_ge_two : 2 ≤ stage1.base := by
  rewrite [stage1]
  exact seed_base_ge_two.trans (resetCounter_base_ge seed)

theorem stage2_base_ge_two : 2 ≤ stage2.base := by
  rewrite [stage2]
  exact stage1_base_ge_two.trans (resetCounter_base_ge stage1)

theorem six_cost_positive (a b c d e f : ℕ) : 0 < 27965+a+b+c+d+e+f := by omega

theorem clockFor_positive (C0 C1 C2 : Counter) : 0<clockFor C0 C1 C2 := by
  unfold clockFor
  exact six_cost_positive _ _ _ _ _ _

attribute [local irreducible] clockFor

theorem exactN_positive : 0<exactN := by
  rewrite [exactN_def]
  exact clockFor_positive seed stage1 stage2

end BeaverStructural.BB6
