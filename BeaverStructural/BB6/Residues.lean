import BeaverStructural.BB6.Bulk
import BeaverStructural.BB6.Clock

namespace BeaverStructural.BB6

/-- Binary modular powering keeps every intermediate below the modulus.
The executable recursion is proved equal to the ordinary exact power. -/
def modularPower (base exponent modulus : ℕ) : ℕ :=
  if h : exponent=0 then 1%modulus else
    let half := modularPower base (exponent/2) modulus
    if exponent%2=0 then (half*half)%modulus else (half*half*base)%modulus
termination_by exponent
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

theorem modularPower_eq (base exponent modulus : ℕ) :
    modularPower base exponent modulus=base^exponent%modulus := by
  induction exponent using Nat.strong_induction_on with
  | h exponent ih =>
    rw [modularPower]
    split_ifs with hz he
    · subst exponent; rfl
    · rw [ih (exponent/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide))]
      have hd : exponent=exponent/2+exponent/2 := by omega
      conv_rhs => rw [hd, pow_add, Nat.mul_mod]
    · rw [ih (exponent/2) (Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide))]
      have hd : exponent=exponent/2+exponent/2+1 := by omega
      conv_rhs => rw [hd, pow_succ, pow_add, Nat.mul_mod, Nat.mul_mod]
      dsimp only
      simp only [Nat.mul_mod, Nat.mod_mod]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem pow2_period_decimal_twenty :
    (2:ℕ)^(20+4*5^19)%10^20=2^20%10^20 := by
  rw [← modularPower_eq, ← modularPower_eq]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem pow2_period_decimal_two_hundred :
    (2:ℕ)^(200+4*5^199)%10^200=2^200%10^200 := by
  rw [← modularPower_eq, ← modularPower_eq]
  decide +kernel

/-- A verified finite modular period extends above its exact cutoff. -/
theorem pow2_period_after_cutoff (m c p r : ℕ)
    (hc : 2^(c+p)%m=2^c%m) : 2^(c+r+p)%m=2^(c+r)%m := by
  rw [show c+r+p=(c+p)+r by omega, pow_add, Nat.mul_mod, hc,
    ← Nat.mul_mod, ← pow_add]

theorem pow2_period_multiple (m c p r q : ℕ)
    (hc : 2^(c+p)%m=2^c%m) : 2^(c+r+q*p)%m=2^(c+r)%m := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc]
    have heq : c+r+q*p=c+(r+q*p) := by omega
    rw [heq, pow2_period_after_cutoff m c p (r+q*p) hc, ← heq, ih]

theorem pow2_mod_reduce (m c p n : ℕ) (hn : c≤n)
    (hc : 2^(c+p)%m=2^c%m) : 2^n%m=2^(c+(n-c)%p)%m := by
  have h := pow2_period_multiple m c p ((n-c)%p) ((n-c)/p) hc
  have heq : c+(n-c)%p+((n-c)/p)*p=n := by
    have hd := Nat.mod_add_div (n-c) p
    rw [Nat.mul_comm p] at hd
    omega
  rw [heq] at h
  exact h

/-- Congruent exponents above a verified cutoff yield the same power residue. -/
theorem pow2_mod_of_congruent (m c p n k : ℕ) (hn : c≤n) (hk : c≤k)
    (hc : 2^(c+p)%m=2^c%m) (he : n%p=k%p) : 2^n%m=2^k%m := by
  rw [pow2_mod_reduce m c p n hn hc, pow2_mod_reduce m c p k hk hc]
  have hsub : (n-c)%p=(k-c)%p := Nat.ModEq.sub hn hk he (Nat.ModEq.refl c)
  rw [hsub]

theorem pow2_period_1000 : (2:ℕ)^(3+100)%1000=2^3%1000 := by norm_num
theorem pow2_period_100 : (2:ℕ)^(2+20)%100=2^2%100 := by norm_num
theorem pow2_period_20 : (2:ℕ)^(2+4)%20=2^2%20 := by norm_num
theorem pow2_period_4 : (2:ℕ)^(2+1)%4=2^2%4 := by norm_num
theorem pow2_period_8 : (2:ℕ)^(3+1)%8=2^3%8 := by norm_num

/-- One exact tower step consumes only a proved residue and a cutoff bound. -/
theorem tower_step_mod_at (m c p h b r : ℕ) (hn : c≤tower h b) (hr : c≤r)
    (hp : 2^(c+p)%m=2^c%m) (he : tower h b%p=r%p) :
    tower (h+1) b%m=(2^r-1)%m := by
  have hh := pow2_mod_of_congruent m c p (tower h b) r hn hr hp he
  have hp1 : 1≤2^tower h b := Nat.one_le_pow _ _ (by norm_num)
  have hp2 : 1≤2^r := Nat.one_le_pow _ _ (by norm_num)
  exact Nat.ModEq.sub hp1 hp2 hh (Nat.ModEq.refl 1)

theorem tower_step_mod (m c p h b r : ℕ) (hb : c≤b) (hr : c≤r)
    (hp : 2^(c+p)%m=2^c%m) (he : tower h b%p=r%p) :
    tower (h+1) b%m=(2^r-1)%m := by
  have hn : c≤tower h b := le_trans hb (le_tower h b)
  exact tower_step_mod_at m c p h b r hn hr hp he

/-- A child modulus stabilizer lifts through one exact Mersenne step.
The whole infinite tail is certified by a finite period equation. -/
theorem tower_stabilizer_lift (m c p cutoff b r out : ℕ)
    (hp : 2^(c+p)%m=2^c%m) (hr : c≤r) (hb : c≤tower cutoff b)
    (child : ∀ j, tower (cutoff+j) b%p=r%p)
    (ho : (2^r-1)%m=out) :
    ∀ j, tower (cutoff+1+j) b%m=out := by
  intro j
  have hn : c≤tower (cutoff+j) b :=
    hb.trans (tower_monotone b (by omega))
  have hs := tower_step_mod_at m c p (cutoff+j) b r hn hr hp (child j)
  rw [show cutoff+j+1=cutoff+1+j by omega, ho] at hs
  exact hs

theorem tower_mod_four_stable (h b : ℕ) (hb : 2≤b) :
    tower (h+1) b%4=3 := by
  have ht := tower_step_mod 4 2 1 h b 2 hb (by omega) pow2_period_4 (Nat.mod_one _)
  exact ht

theorem tower_mod_eight_stable (h b : ℕ) (hb : 3≤b) :
    tower (h+1) b%8=7 := by
  exact tower_step_mod 8 3 1 h b 3 hb (by omega) pow2_period_8 (Nat.mod_one _)

theorem tower_mod_twenty_stable (h b : ℕ) (hb : 3≤b) :
    tower (h+2) b%20=7 := by
  have ht := tower_step_mod 20 2 4 (h+1) b 3 (by omega) (by omega)
    pow2_period_20 (tower_mod_four_stable h b (by omega))
  exact ht

theorem tower_mod_hundred_stable (h b : ℕ) (hb : 3≤b) :
    tower (h+3) b%100=27 := by
  have ht := tower_step_mod 100 2 20 (h+2) b 7 (by omega) (by omega)
    pow2_period_100 (tower_mod_twenty_stable h b hb)
  exact ht

theorem tower_mod_thousand_stable (h b : ℕ) (hb : 3≤b) :
    tower (h+4) b%1000=727 := by
  have ht := tower_step_mod 1000 3 100 (h+3) b 27 hb (by omega)
    pow2_period_1000 (tower_mod_hundred_stable h b hb)
  exact ht

/-- A finite prefix plus an arbitrarily long certified constant residue tail. -/
theorem sum_mod_constant_tail (f : ℕ→ℕ) (m cutoff count r : ℕ)
    (h : ∀ j, f (cutoff+j)%m=r%m) :
    (∑ j ∈ Finset.range (cutoff+count), f j)%m =
      ((∑ j ∈ Finset.range cutoff, f j)+count*r)%m := by
  rw [Finset.sum_range_add]
  have hs : (∑ j ∈ Finset.range count, f (cutoff+j))%m=(count*r)%m := by
    rw [Finset.sum_nat_mod]
    simp_rw [h]
    simp [Nat.mul_mod]
  rw [Nat.add_mod, hs, ← Nat.add_mod]

theorem twice_descending_sum (count : ℕ) :
    2*(∑ j ∈ Finset.range count, (count-j))=count*(count+1) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero, Nat.mul_add, ih]
    ring

/-- Weighted tails are read with one exact triangular polynomial. Multiplying
by two preserves the division carry rather than dropping an odd remainder. -/
theorem twice_weighted_sum_mod_constant_tail (f : ℕ→ℕ) (m cutoff count r : ℕ)
    (h : ∀ j, f (cutoff+j)%m=r%m) :
    (2*(∑ j ∈ Finset.range (cutoff+count), (cutoff+count-j)*f j))%m =
      (2*(∑ j ∈ Finset.range cutoff, (cutoff+count-j)*f j)+count*(count+1)*r)%m := by
  rw [Finset.sum_range_add, Nat.mul_add]
  have hs : (∑ j ∈ Finset.range count, (cutoff+count-(cutoff+j))*f (cutoff+j))%m =
      ((∑ j ∈ Finset.range count, (count-j))*r)%m := by
    conv_lhs => rw [Finset.sum_nat_mod]
    conv_rhs => rw [Finset.sum_mul, Finset.sum_nat_mod]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_sub_add_left, Nat.mul_mod, h, ← Nat.mul_mod]
  have htwice := Nat.ModEq.mul_left 2 hs
  rw [← Nat.mul_assoc, twice_descending_sum] at htwice
  exact Nat.ModEq.add_left _ htwice

theorem towerSum_mod_constant (n b m r : ℕ) (h : ∀ j, tower j b%m=r%m) :
    towerSum n b%m=(n*r)%m := by
  have hs := sum_mod_constant_tail (fun j => tower j b) m 0 n r
    (fun j => by simpa only [Nat.zero_add] using h j)
  simpa only [Nat.zero_add, Finset.range_zero, Finset.sum_empty, towerSum] using hs

theorem towerSquareSum_mod_constant (n b m r : ℕ) (h : ∀ j, tower j b%m=r%m) :
    towerSquareSum n b%m=(n*r^2)%m := by
  have hp : ∀ j, (tower j b)^2%m=(r^2)%m := fun j => Nat.ModEq.pow 2 (h j)
  have hs := sum_mod_constant_tail (fun j => (tower j b)^2) m 0 n (r^2)
    (fun j => by simpa only [Nat.zero_add] using hp j)
  simpa only [Nat.zero_add, Finset.range_zero, Finset.sum_empty, towerSquareSum] using hs

theorem towerWeightedSum_twice_mod_constant (n b m r : ℕ)
    (h : ∀ j, tower j b%m=r%m) :
    (2*towerWeightedSum n b)%m=(n*(n+1)*r)%m := by
  have hs := twice_weighted_sum_mod_constant_tail (fun j => tower j b) m 0 n r
    (fun j => by simpa only [Nat.zero_add] using h j)
  simpa only [Nat.zero_add, Finset.range_zero, Finset.sum_empty, Nat.mul_zero,
    towerWeightedSum] using hs

theorem bulkCost_mod_constant (n b m r : ℕ) (h : ∀ j, tower j b%m=r%m) :
    bulkCost n b%m=
      (6*n*r^2+45*n*r+6*n*(n+1)*r+10*n^2+61*n+12*binaryCarry n)%m := by
  have hshift : ∀ j, tower j (tower 2 b)%m=r%m := by
    intro j
    rw [← tower_add]
    exact h (j+2)
  have hs := towerSquareSum_mod_constant n (tower 2 b) m r hshift
  have hl := towerSum_mod_constant n (tower 2 b) m r hshift
  have hw := Nat.ModEq.mul_left 6 (towerWeightedSum_twice_mod_constant n b m r h)
  have hd : (tower (n+1) b-tower 1 b)%m=0%m := by
    simpa only [Nat.sub_self] using
      Nat.ModEq.sub (tower_monotone b (by omega : 1≤n+1)) (le_refl r) (h (n+1)) (h 1)
  have hc := (Nat.ModEq.mul_left 6 hs).add (Nat.ModEq.mul_left 45 hl)
  have hc := (hc.add (Nat.ModEq.mul_left 9 hd)).add hw
  have hc := ((hc.add (Nat.ModEq.refl (10*n^2))).add
    (Nat.ModEq.refl (61*n))).add (Nat.ModEq.refl (12*binaryCarry n))
  norm_num only [Nat.ModEq, bulkCost, Nat.mul_zero, Nat.add_zero, ← Nat.mul_assoc] at hc ⊢
  exact hc

attribute [local irreducible] tower towerSum towerSquareSum towerWeightedSum
  exhaustedWidth exhaustedRight resetCounter stage1 stage2

theorem phaseCost_mod_eight (n b j : ℕ) (hb : 3≤b) :
    phaseCost n b j%8=(4*b+4*padicValNat 2 (n-j))%8 := by
  have h1 := tower_mod_eight_stable j b hb
  have h2 : tower (j+2) b%8=7 := tower_mod_eight_stable (j+1) b hb
  have hd : (tower (j+2) b-tower (j+1) b)%8=0 :=
    Nat.ModEq.sub (tower_step_mono (j+1) b) (by omega : 7≤7) h2 h1
  have hs : (tower (j+2) b)^2%8=1 := by rw [Nat.pow_mod, h2]
  have hp := towerSum_parity j b (by omega)
  unfold phaseCost
  omega

theorem bulkCost_mod_eight (n b : ℕ) (hb : 3≤b) :
    bulkCost n b%8=(4*n*b+4*binaryCarry n)%8 := by
  rw [bulkCost_eq_sum_phaseCost, Finset.sum_nat_mod]
  simp_rw [phaseCost_mod_eight n b _ hb]
  rw [← Finset.sum_nat_mod, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum, reverse_binary_carry_sum]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  congr 1
  ring

theorem exhaustedWidth_positive (C : Counter) : 0<exhaustedWidth C := by
  unfold exhaustedWidth
  split_ifs <;> omega

theorem resetCounter_count_odd (C : Counter) : (resetCounter C).count%2=1 := by
  rewrite [resetCounter_count]
  have hp := pow_two_mod_two (exhaustedWidth C) (exhaustedWidth_positive C)
  have hmul : ((2^(C.length+2)-1)*2^exhaustedWidth C)%2=0 := by
    rw [Nat.mul_mod, hp]
    omega
  have hleft : 0<2^(C.length+2)-1 := by have := self_lt_two_pow (C.length+2); omega
  have hright : 0<(2:ℕ)^exhaustedWidth C := by positivity
  have hprod := Nat.mul_pos hleft hright
  omega

theorem resetCounter_base_odd (C : Counter) (hb : 0<C.base) :
    (resetCounter C).base%2=1 := by
  rewrite [resetCounter_base, exhaustedRight]
  exact tower_succ_odd C.count C.base hb

theorem resetCounter_population (C : Counter) :
    binaryPopulation (resetCounter C).count=C.length+exhaustedWidth C+1 := by
  rewrite [resetCounter_count]
  exact binaryPopulation_reset C.length (exhaustedWidth C)

theorem width_parity_one (C : Counter) (hb : C.base%2=1)
    (hn : C.count%2=1) (hr : C.count%3=1) : exhaustedWidth C%2=0 := by
  rw [exhaustedWidth_parity C (by omega), hr, if_pos rfl]
  omega

theorem width_parity_two (C : Counter) (hb : C.base%2=1)
    (hn : C.count%2=1) (hr : C.count%3=2) : exhaustedWidth C%2=1 := by
  rw [exhaustedWidth_parity C (by omega), hr, if_neg (by decide)]
  omega

theorem stage1_base_odd : stage1.base%2=1 := by
  rewrite [stage1]
  exact resetCounter_base_odd seed (by decide)
theorem stage2_base_odd : stage2.base%2=1 := by
  rewrite [stage2]
  exact resetCounter_base_odd stage1 (by have := stage1_base_ge_two; omega)
theorem stage1_count_odd : stage1.count%2=1 := by
  rewrite [stage1]
  exact resetCounter_count_odd seed
theorem stage2_count_odd : stage2.count%2=1 := by
  rewrite [stage2]
  exact resetCounter_count_odd stage1
theorem stage1_width_even : exhaustedWidth stage1%2=0 :=
  width_parity_one stage1 stage1_base_odd stage1_count_odd stage1_residue
theorem stage2_width_odd : exhaustedWidth stage2%2=1 :=
  width_parity_two stage2 stage2_base_odd stage2_count_odd stage2_residue

theorem reset_length_even (C : Counter) (hL : C.length%2=0)
    (ha : exhaustedWidth C%2=0) : (resetCounter C).length%2=0 := by
  rewrite [resetCounter_length]
  omega
theorem stage2_length_even : stage2.length%2=0 := by
  rewrite [stage2]
  exact reset_length_even stage1 stage1_length_even stage1_width_even

theorem stage1_base_ge_three : 3≤stage1.base := by
  rewrite [stage1]
  exact (show 3≤seed.base by decide).trans (resetCounter_base_ge seed)
theorem stage2_base_ge_three : 3≤stage2.base := by
  rewrite [stage2]
  exact stage1_base_ge_three.trans (resetCounter_base_ge stage1)

theorem bulkCost_mod_eight_odd_base (n b : ℕ) (hb : 3≤b) (hodd : b%2=1) :
    bulkCost n b%8=(4*binaryPopulation n)%8 := by
  rw [bulkCost_mod_eight n b hb, show 4*n*b=4*(n*b) by ring]
  have hprod : (n*b)%2=n%2 := by rw [Nat.mul_mod, hodd]; simp
  have hpop := population_le n
  unfold binaryCarry
  omega

theorem resetCost_mod_eight (L a b : ℕ) (hb : 3≤b) (hr : b%8=7) :
    resetCost L a b%8=(2+4*L+4*a)%8 := by
  have hs : (2^b-1)%8=7 := by
    simpa only [tower_succ, tower_zero] using tower_mod_eight_stable 0 b hb
  have hsq : (2^b-1)^2%8=1 := by rw [Nat.pow_mod, hs]
  have hle : b≤2^b-1 := by have := self_lt_two_pow b; omega
  have hd : (2^b-1-b)%8=0 := Nat.ModEq.sub hle (by omega : 7≤7) hs hr
  dsimp only [resetCost]
  omega

theorem reset_cost_counter_mod_eight (C : Counter) (hb : 3≤C.base) :
    resetCost C.length (exhaustedWidth C) (exhaustedRight C)%8=
      (2+4*C.length+4*exhaustedWidth C)%8 := by
  have hge : 3≤exhaustedRight C := by
    unfold exhaustedRight
    exact hb.trans (le_tower _ _)
  have hmod : exhaustedRight C%8=7 := by
    unfold exhaustedRight
    exact tower_mod_eight_stable C.count C.base hb
  exact resetCost_mod_eight _ _ _ hge hmod

theorem reset_cost_same_parity (C : Counter) (hb : 3≤C.base)
    (he : C.length%2=exhaustedWidth C%2) :
    resetCost C.length (exhaustedWidth C) (exhaustedRight C)%8=2 := by
  rw [reset_cost_counter_mod_eight C hb]
  omega

theorem reset_population_odd (C : Counter)
    (he : C.length%2=exhaustedWidth C%2) :
    binaryPopulation (resetCounter C).count%2=1 := by
  rw [resetCounter_population]
  omega

theorem bulkCost_mod_eight_odd_population (C : Counter) (hb : 3≤C.base)
    (hbo : C.base%2=1) (hp : binaryPopulation C.count%2=1) :
    bulkCost C.count C.base%8=4 := by
  rw [bulkCost_mod_eight_odd_base _ _ hb hbo]
  omega

theorem halt_cost_even_length_odd_width (C : Counter)
    (hL : C.length%2=0) (ha : exhaustedWidth C%2=1) :
    haltCost C.length (exhaustedWidth C)%8=0 := by
  unfold haltCost
  omega

attribute [local irreducible] bulkCost resetCost haltCost

theorem seed_bulk_mod_eight : bulkCost seed.count seed.base%8=0 := by
  have hsmall : (4*7*6+4*binaryCarry 7)%8=0 := by decide
  exact (bulkCost_mod_eight seed.count seed.base (by decide)).trans hsmall

theorem seed_reset_mod_eight :
    resetCost seed.length (exhaustedWidth seed) (exhaustedRight seed)%8=2 := by
  exact reset_cost_same_parity seed (by decide) seed_width_odd.symm

theorem stage1_population_odd : binaryPopulation stage1.count%2=1 := by
  rewrite [stage1]
  exact reset_population_odd seed seed_width_odd.symm

theorem stage2_population_odd : binaryPopulation stage2.count%2=1 := by
  rewrite [stage2]
  exact reset_population_odd stage1 (stage1_length_even.trans stage1_width_even.symm)

theorem stage1_bulk_mod_eight : bulkCost stage1.count stage1.base%8=4 :=
  bulkCost_mod_eight_odd_population stage1 stage1_base_ge_three stage1_base_odd
    stage1_population_odd
theorem stage2_bulk_mod_eight : bulkCost stage2.count stage2.base%8=4 :=
  bulkCost_mod_eight_odd_population stage2 stage2_base_ge_three stage2_base_odd
    stage2_population_odd
theorem stage1_reset_mod_eight :
    resetCost stage1.length (exhaustedWidth stage1) (exhaustedRight stage1)%8=2 :=
  reset_cost_same_parity stage1 stage1_base_ge_three
    (stage1_length_even.trans stage1_width_even.symm)
theorem stage2_halt_mod_eight : haltCost stage2.length (exhaustedWidth stage2)%8=0 :=
  halt_cost_even_length_odd_width stage2 stage2_length_even stage2_width_odd

theorem six_cost_mod_eight (a b c d e f : ℕ)
    (ha : a%8=0) (hb : b%8=2) (hc : c%8=4) (hd : d%8=2)
    (he : e%8=4) (hf : f%8=0) : (27965+a+b+c+d+e+f)%8=1 := by omega

theorem clockFor_mod_eight (C0 C1 C2 : Counter)
    (h0 : bulkCost C0.count C0.base%8=0)
    (h1 : resetCost C0.length (exhaustedWidth C0) (exhaustedRight C0)%8=2)
    (h2 : bulkCost C1.count C1.base%8=4)
    (h3 : resetCost C1.length (exhaustedWidth C1) (exhaustedRight C1)%8=2)
    (h4 : bulkCost C2.count C2.base%8=4)
    (h5 : haltCost C2.length (exhaustedWidth C2)%8=0) :
    clockFor C0 C1 C2%8=1 := by
  unfold clockFor
  exact six_cost_mod_eight _ _ _ _ _ _ h0 h1 h2 h3 h4 h5

theorem bulkCost_mod_three (n b : ℕ) :
    bulkCost n b % 3 = (n^2+n)%3 := by
  unfold bulkCost
  omega

theorem resetCost_mod_three (L a b : ℕ) : resetCost L a b % 3 = 1 := by
  unfold resetCost
  dsimp only
  omega

theorem haltCost_mod_three (L a : ℕ) : haltCost L a % 3 = 0 := by
  simp [haltCost, Nat.add_mod, Nat.mul_mod]

theorem bulkCost_mod_three_one (n b : ℕ) (hn : n%3=1) : bulkCost n b%3=2 := by
  rw [bulkCost_mod_three, Nat.add_mod, Nat.pow_mod, hn]

theorem bulkCost_mod_three_two (n b : ℕ) (hn : n%3=2) : bulkCost n b%3=0 := by
  rw [bulkCost_mod_three, Nat.add_mod, Nat.pow_mod, hn]

theorem six_cost_mod_three (a b c d e f : ℕ)
    (ha : a%3=2) (hb : b%3=1) (hc : c%3=2) (hd : d%3=1)
    (he : e%3=0) (hf : f%3=0) : (27965+a+b+c+d+e+f)%3=2 := by omega

/-- A residue of the actual explicit clock expression, without materializing N. -/
theorem clockFor_mod_three (C0 C1 C2 : Counter)
    (h0 : C0.count%3=1) (h1 : C1.count%3=1) (h2 : C2.count%3=2) :
    clockFor C0 C1 C2%3=2 := by
  unfold clockFor
  exact six_cost_mod_three
    (bulkCost C0.count C0.base)
    (resetCost C0.length (exhaustedWidth C0) (exhaustedRight C0))
    (bulkCost C1.count C1.base)
    (resetCost C1.length (exhaustedWidth C1) (exhaustedRight C1))
    (bulkCost C2.count C2.base)
    (haltCost C2.length (exhaustedWidth C2))
    (bulkCost_mod_three_one C0.count C0.base h0)
    (resetCost_mod_three C0.length (exhaustedWidth C0) (exhaustedRight C0))
    (bulkCost_mod_three_one C1.count C1.base h1)
    (resetCost_mod_three C1.length (exhaustedWidth C1) (exhaustedRight C1))
    (bulkCost_mod_three_two C2.count C2.base h2)
    (haltCost_mod_three C2.length (exhaustedWidth C2))

attribute [local irreducible] clockFor

theorem exactN_mod_three : exactN%3=2 := by
  rewrite [exactN_def]
  exact clockFor_mod_three seed stage1 stage2 seed_residue stage1_residue stage2_residue

theorem exactN_mod_eight : exactN%8=1 := by
  rewrite [exactN_def]
  exact clockFor_mod_eight seed stage1 stage2 seed_bulk_mod_eight seed_reset_mod_eight
    stage1_bulk_mod_eight stage1_reset_mod_eight stage2_bulk_mod_eight stage2_halt_mod_eight

end BeaverStructural.BB6
