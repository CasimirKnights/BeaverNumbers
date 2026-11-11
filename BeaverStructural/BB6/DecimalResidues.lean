import BeaverStructural.BB6.Residues

set_option compiler.extract_closed false

namespace BeaverStructural.BB6

attribute [local irreducible] tower towerSum towerSquareSum towerWeightedSum
  exhaustedWidth exhaustedRight resetCounter stage1 stage2 bulkCost resetCost haltCost clockFor

theorem tower_reset_base (C : Counter) (h : ℕ) :
    tower h (resetCounter C).base=tower (h+(C.count+1)) C.base := by
  rewrite [resetCounter_base, exhaustedRight]
  exact (tower_add h (C.count+1) C.base).symm


theorem tower_stage1 (h : ℕ) : tower h stage1.base=tower (h+8) 6 := by
  rewrite [stage1]
  exact tower_reset_base seed h


theorem stage1_towers_mod_thousand (h : ℕ) : tower h stage1.base%1000=727 := by
  rw [tower_stage1]
  exact tower_mod_thousand_stable (h+4) 6 (by decide)


theorem tower_reset_mod_constant (C : Counter) (m r : ℕ)
    (h : ∀ j, tower j C.base%m=r) (j : ℕ) : tower j (resetCounter C).base%m=r := by
  rw [tower_reset_base]
  exact h _


theorem stage2_towers_mod_thousand (h : ℕ) : tower h stage2.base%1000=727 := by
  rewrite [stage2]
  exact tower_reset_mod_constant stage1 1000 727 stage1_towers_mod_thousand h


theorem exhaustedWidth_ge_base (C : Counter) : C.base≤exhaustedWidth C := by
  unfold exhaustedWidth
  rw [towerSum_succ]
  have ht := le_tower C.count C.base
  split_ifs <;> omega


theorem seed_width_ge_six : 6≤exhaustedWidth seed := exhaustedWidth_ge_base seed

theorem stage1_width_ge_three : 3≤exhaustedWidth stage1 :=
  stage1_base_ge_three.trans (exhaustedWidth_ge_base stage1)


theorem seed_tower_two_mod_thousand : tower 2 6%1000=807 := by
  rw [tower_succ, tower_succ, tower_zero]
  have h : (2:ℕ)^63%1000=808 := by
    rw [← modularPower_eq]
    decide +kernel
  have hp : 0<(2:ℕ)^63 := by positivity
  norm_num only [Nat.reducePow] at *

theorem tower_step_thousand_seven (h b : ℕ) (hb : 3≤b)
    (he : tower h b%100=7) : tower (h+1) b%1000=127 := by
  exact tower_step_mod 1000 3 100 h b 7 hb (by decide) pow2_period_1000 he

theorem mod_thousand_to_hundred (n r : ℕ) (h : n%1000=r) : n%100=r%100 := by omega

theorem seed_tower_three_mod_thousand : tower (2+1) 6%1000=127 :=
  tower_step_thousand_seven 2 6 (by decide)
    (mod_thousand_to_hundred (tower 2 6) 807 seed_tower_two_mod_thousand)


theorem towerSum_eight (b : ℕ) : towerSum 8 b=
    tower 0 b+tower 1 b+tower 2 b+tower 3 b+tower 4 b+tower 5 b+tower 6 b+tower 7 b := by
  norm_num only [towerSum, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]


theorem width_seed_shape (b : ℕ) : exhaustedWidth ⟨3,7,b⟩=towerSum 8 b+12 := by
  unfold exhaustedWidth
  norm_num only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul, ↓reduceIte, ite_true]


theorem width_seed_mod (b : ℕ)
    (h0 : tower 0 b%1000=6) (h1 : tower 1 b%1000=63)
    (h2 : tower 2 b%1000=807) (h3 : tower (2+1) b%1000=127)
    (ht : ∀ h, tower (h+4) b%1000=727) : exhaustedWidth ⟨3,7,b⟩%1000=923 := by
  have h4 := ht 0
  have h5 := ht 1
  have h6 := ht 2
  have h7 := ht 3
  simp only [Nat.reduceAdd] at h3 h4 h5 h6 h7
  rw [width_seed_shape, towerSum_eight]
  omega


theorem width_seed_transfer (C : Counter) (b : ℕ)
    (hC : C=⟨3,7,b⟩) (h : exhaustedWidth ⟨3,7,b⟩%1000=923) :
    exhaustedWidth C%1000=923 := by rw [hC]; exact h

theorem seed_width_mod_thousand : exhaustedWidth seed%1000=923 :=
  width_seed_transfer seed 6 rfl
    (width_seed_mod 6 (by rw [tower_zero])
      (by rw [tower_succ,tower_zero]; decide)
      seed_tower_two_mod_thousand seed_tower_three_mod_thousand
      (fun h => tower_mod_thousand_stable h 6 (by decide)))


theorem seed_width_mod_hundred : exhaustedWidth seed%100=23 :=
  mod_thousand_to_hundred (exhaustedWidth seed) 923 seed_width_mod_thousand


theorem power_seed_width_mod_thousand : 2^exhaustedWidth seed%1000=608 := by
  exact (pow2_mod_of_congruent 1000 3 100 (exhaustedWidth seed) 23
    (by have := seed_width_ge_six; omega) (by decide) pow2_period_1000
    seed_width_mod_hundred).trans (by decide)


theorem reset_count_mod (L a : ℕ) (hL : 2^(L+2)%1000=32)
    (ha : 2^a%1000=608) : ((2^(L+2)-1)*2^a-1)%1000=847 := by
  have hp : 0<2^(L+2)-1 := by have := self_lt_two_pow (L+2); omega
  have hq : 0<(2:ℕ)^a := by positivity
  have hprod := Nat.mul_pos hp hq
  have hpred : (2^(L+2)-1)%1000=31 := by omega
  have hm : ((2^(L+2)-1)*2^a)%1000=848 := by rw [Nat.mul_mod,hpred,ha]
  omega


theorem stage1_count_mod_thousand : stage1.count%1000=847 := by
  rewrite [stage1, resetCounter_count]
  exact reset_count_mod seed.length (exhaustedWidth seed) (by decide)
    power_seed_width_mod_thousand


theorem stage1_length_mod_thousand : stage1.length%1000=928 := by
  have h : ∀ L a : ℕ, L%1000=3 → a%1000=923 → (L+a+2)%1000=928 := by intro L a hL ha; omega
  rewrite [stage1, resetCounter_length]
  exact h seed.length (exhaustedWidth seed) (by decide) seed_width_mod_thousand


theorem width_mod_of_constant_towers (C : Counter) (nr qr r out : ℕ)
    (ht : ∀ j, tower j C.base%1000=727)
    (hn : C.count%1000=nr) (hq : (C.count/3)%1000=qr) (hr : C.count%3=r)
    (hout : ((nr+1)*727+5*qr+(if r=1 then 2 else 4))%1000=out) :
    exhaustedWidth C%1000=out := by
  have hs := towerSum_mod_constant (C.count+1) C.base 1000 727 ht
  have hv : towerSum (C.count+1) C.base%1000=((nr+1)*727)%1000 := by
    rw [hs]
    have hnr : nr%1000=nr := by omega
    simp only [Nat.mul_mod, Nat.add_mod, hn, hnr, Nat.mod_mod]
  unfold exhaustedWidth
  rw [hr]
  have hqr : qr%1000=qr := by omega
  simpa only [Nat.add_mod, Nat.mul_mod, hv, hq, hqr, Nat.mod_mod] using hout


theorem stage1_div_count_mod_thousand : (stage1.count/3)%1000=282 := by
  have h : ∀ n : ℕ, n%1000=847 → n%3=1 → (n/3)%1000=282 := by
    intro n hn hr
    omega
  exact h _ stage1_count_mod_thousand stage1_residue


theorem stage1_width_mod_thousand : exhaustedWidth stage1%1000=908 :=
  width_mod_of_constant_towers stage1 847 282 1 908 stage1_towers_mod_thousand
    stage1_count_mod_thousand stage1_div_count_mod_thousand stage1_residue (by decide)

theorem stage1_width_mod_hundred : exhaustedWidth stage1%100=8 :=
  mod_thousand_to_hundred (exhaustedWidth stage1) 908 stage1_width_mod_thousand

theorem stage1_length_plus_two_mod_hundred : (stage1.length+2)%100=30 := by
  have h : ∀ L : ℕ, L%1000=928 → (L+2)%100=30 := by intro L hL; omega
  exact h _ stage1_length_mod_thousand

theorem stage1_length_plus_two_ge_three : 3≤stage1.length+2 := by
  have h : ∀ C : Counter, 3≤(resetCounter C).length+2 := by
    intro C
    rewrite [resetCounter_length]
    omega
  rewrite [stage1]
  exact h seed

theorem power_stage1_length_mod_thousand : 2^(stage1.length+2)%1000=824 := by
  have hsmall : (2:ℕ)^30%1000=824 := by decide
  exact (pow2_mod_of_congruent 1000 3 100 (stage1.length+2) 30
    stage1_length_plus_two_ge_three (by decide) pow2_period_1000
    stage1_length_plus_two_mod_hundred).trans hsmall

theorem power_stage1_width_mod_thousand : 2^exhaustedWidth stage1%1000=256 := by
  have hsmall : (2:ℕ)^8%1000=256 := by decide
  exact (pow2_mod_of_congruent 1000 3 100 (exhaustedWidth stage1) 8
    stage1_width_ge_three (by decide) pow2_period_1000
    stage1_width_mod_hundred).trans hsmall

theorem second_reset_count_mod (L a : ℕ) (hL : 2^(L+2)%1000=824)
    (ha : 2^a%1000=256) : ((2^(L+2)-1)*2^a-1)%1000=687 := by
  have hp : 0<2^(L+2)-1 := by have := self_lt_two_pow (L+2); omega
  have hq : 0<(2:ℕ)^a := by positivity
  have hprod := Nat.mul_pos hp hq
  have hpred : (2^(L+2)-1)%1000=823 := by omega
  have hm : ((2^(L+2)-1)*2^a)%1000=688 := by rw [Nat.mul_mod,hpred,ha]
  omega

theorem stage2_count_mod_thousand : stage2.count%1000=687 := by
  rewrite [stage2, resetCounter_count]
  exact second_reset_count_mod stage1.length (exhaustedWidth stage1)
    power_stage1_length_mod_thousand power_stage1_width_mod_thousand

theorem stage2_length_mod_thousand : stage2.length%1000=838 := by
  have h : ∀ L a : ℕ, L%1000=928 → a%1000=908 → (L+a+2)%1000=838 := by
    intro L a hL ha
    omega
  rewrite [stage2, resetCounter_length]
  exact h _ _ stage1_length_mod_thousand stage1_width_mod_thousand

theorem stage2_div_count_mod_thousand : (stage2.count/3)%1000=895 := by
  have h : ∀ n : ℕ, n%1000=687 → n%3=2 → (n/3)%1000=895 := by
    intro n hn hr
    omega
  exact h _ stage2_count_mod_thousand stage2_residue

theorem stage2_width_mod_thousand : exhaustedWidth stage2%1000=655 :=
  width_mod_of_constant_towers stage2 687 895 2 655 stage2_towers_mod_thousand
    stage2_count_mod_thousand stage2_div_count_mod_thousand stage2_residue (by decide)

theorem reset_population_mod (C : Counter) (lr ar : ℕ)
    (hL : C.length%1000=lr) (ha : exhaustedWidth C%1000=ar) :
    binaryPopulation (resetCounter C).count%1000=(lr+ar+1)%1000 := by
  rw [resetCounter_population]
  omega

theorem stage1_population_mod_thousand : binaryPopulation stage1.count%1000=927 := by
  rewrite [stage1]
  exact reset_population_mod seed 3 923 (by decide) seed_width_mod_thousand

theorem stage2_population_mod_thousand : binaryPopulation stage2.count%1000=837 := by
  rewrite [stage2]
  exact reset_population_mod stage1 928 908 stage1_length_mod_thousand stage1_width_mod_thousand

theorem carry_mod_from_population (n nr pr out : ℕ) (hn : n%1000=nr)
    (hp : binaryPopulation n%1000=pr)
    (ho : (nr+1000-pr)%1000=out) (hr : pr<1000) : binaryCarry n%1000=out := by
  have hb := population_le n
  unfold binaryCarry
  omega

theorem stage1_carry_mod_thousand : binaryCarry stage1.count%1000=920 :=
  carry_mod_from_population stage1.count 847 927 920 stage1_count_mod_thousand
    stage1_population_mod_thousand (by decide) (by decide)
theorem stage2_carry_mod_thousand : binaryCarry stage2.count%1000=850 :=
  carry_mod_from_population stage2.count 687 837 850 stage2_count_mod_thousand
    stage2_population_mod_thousand (by decide) (by decide)

theorem bulk_constant_mod_thousand (C : Counter) (nr cr out : ℕ)
    (ht : ∀ j, tower j C.base%1000=727)
    (hn : C.count%1000=nr) (hc : binaryCarry C.count%1000=cr)
    (ho : (6*nr*727^2+45*nr*727+6*nr*(nr+1)*727+10*nr^2+61*nr+12*cr)%1000=out) :
    bulkCost C.count C.base%1000=out := by
  rw [bulkCost_mod_constant _ _ 1000 727 ht]
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hn, hc, Nat.mod_mod] using ho

theorem stage1_bulk_mod_thousand : bulkCost stage1.count stage1.base%1000=452 :=
  bulk_constant_mod_thousand stage1 847 920 452 stage1_towers_mod_thousand
    stage1_count_mod_thousand stage1_carry_mod_thousand (by decide)
theorem stage2_bulk_mod_thousand : bulkCost stage2.count stage2.base%1000=12 :=
  bulk_constant_mod_thousand stage2 687 850 12 stage2_towers_mod_thousand
    stage2_count_mod_thousand stage2_carry_mod_thousand (by decide)


theorem reset_cost_mod_thousand (L a b lr ar out : ℕ)
    (hb : b%1000=727) (hs : (2^b-1)%1000=727)
    (hL : L%1000=lr) (ha : a%1000=ar)
    (ho : (6*727^2+45*727+12*lr+12*ar+97)%1000=out) :
    resetCost L a b%1000=out := by
  have hbs : b≤2^b-1 := by have := self_lt_two_pow b; omega
  have hd : (2^b-1-b)%1000=0 := by omega
  unfold resetCost
  dsimp only
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hb, hs, hd, hL, ha,
    Nat.mul_zero, Nat.add_zero, Nat.mod_mod] using ho

theorem halt_cost_mod_thousand (L a lr ar out : ℕ)
    (hL : L%1000=lr) (ha : a%1000=ar) (ho : (12*lr+12*ar+60)%1000=out) :
    haltCost L a%1000=out := by
  unfold haltCost
  simpa only [Nat.add_mod, Nat.mul_mod, hL, ha, Nat.mod_mod] using ho


theorem seed_bulk_residue (b : ℕ)
    (h0 : tower 0 b%1000=6) (h1 : tower 1 b%1000=63)
    (h2 : tower 2 b%1000=807) (h3 : tower (2+1) b%1000=127)
    (ht : ∀ h, tower (h+4) b%1000=727) : bulkCost 7 b%1000=584 := by
  have h4 := ht 0
  have h5 := ht 1
  have h6 := ht 2
  have h7 := ht 3
  have h8 := ht 4
  simp only [Nat.reduceAdd] at h3 h4 h5 h6 h7 h8
  have hle : tower 1 b≤tower 8 b := tower_monotone b (by decide)
  have hd : (tower 8 b-tower 1 b)%1000=664 := by omega
  have hc : binaryCarry 7=4 := by decide
  unfold bulkCost
  simp only [towerSquareSum,towerWeightedSum,towerSum,Finset.sum_range_succ,
    Finset.sum_range_zero,← tower_add,Nat.reduceAdd,Nat.reduceSub,Nat.reduceMul,
    Nat.zero_add,Nat.add_zero,Nat.mul_zero,Nat.zero_mul,Nat.mul_one]
  simp only [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,Nat.mod_mod,h0,h1,h2,h3,h4,h5,h6,h7,h8,hd,hc]

theorem bulk_seed_transfer (C : Counter) (b : ℕ) (hn : C.count=7) (hb : C.base=b)
    (h : bulkCost 7 b%1000=584) : bulkCost C.count C.base%1000=584 := by rw [hn,hb]; exact h

theorem seed_bulk_mod_thousand : bulkCost seed.count seed.base%1000=584 :=
  bulk_seed_transfer seed 6 rfl rfl
    (seed_bulk_residue 6 (by rw [tower_zero])
      (by rw [tower_succ,tower_zero]; decide)
      seed_tower_two_mod_thousand seed_tower_three_mod_thousand
      (fun h => tower_mod_thousand_stable h 6 (by decide)))


theorem tower_mod_after_four (b n : ℕ) (hn : 4≤n)
    (ht : ∀ h, tower (h+4) b%1000=727) : tower n b%1000=727 := by
  have he : n=(n-4)+4 := by omega
  rw [he]
  exact ht _

theorem reset_cost_from_stable_towers (C : Counter) (lr ar out : ℕ)
    (hn : 3≤C.count) (ht : ∀ h, tower (h+4) C.base%1000=727)
    (hL : C.length%1000=lr) (ha : exhaustedWidth C%1000=ar)
    (ho : (6*727^2+45*727+12*lr+12*ar+97)%1000=out) :
    resetCost C.length (exhaustedWidth C) (exhaustedRight C)%1000=out := by
  have hb : exhaustedRight C%1000=727 := by
    unfold exhaustedRight
    exact tower_mod_after_four C.base (C.count+1) (by omega) ht
  have hs : (2^exhaustedRight C-1)%1000=727 := by
    unfold exhaustedRight
    rw [← tower_succ]
    exact tower_mod_after_four C.base (C.count+1+1) (by omega) ht
  exact reset_cost_mod_thousand _ _ _ lr ar out hb hs hL ha ho

theorem seed_reset_mod_thousand :
    resetCost seed.length (exhaustedWidth seed) (exhaustedRight seed)%1000=98 :=
  reset_cost_from_stable_towers seed 3 923 98 (by decide)
    (fun h => tower_mod_thousand_stable h seed.base (by decide))
    (by decide) seed_width_mod_thousand (by decide)

theorem stage1_reset_mod_thousand :
    resetCost stage1.length (exhaustedWidth stage1) (exhaustedRight stage1)%1000=18 := by
  have hn : 3≤stage1.count := by have := stage1_count_mod_thousand; omega
  exact reset_cost_from_stable_towers stage1 928 908 18 hn
    (fun h => stage1_towers_mod_thousand (h+4))
    stage1_length_mod_thousand stage1_width_mod_thousand (by decide)

theorem stage2_halt_mod_thousand : haltCost stage2.length (exhaustedWidth stage2)%1000=976 :=
  halt_cost_mod_thousand _ _ 838 655 976 stage2_length_mod_thousand
    stage2_width_mod_thousand (by decide)

theorem clockFor_mod_thousand (C0 C1 C2 : Counter)
    (h0 : bulkCost C0.count C0.base%1000=584)
    (r0 : resetCost C0.length (exhaustedWidth C0) (exhaustedRight C0)%1000=98)
    (h1 : bulkCost C1.count C1.base%1000=452)
    (r1 : resetCost C1.length (exhaustedWidth C1) (exhaustedRight C1)%1000=18)
    (h2 : bulkCost C2.count C2.base%1000=12)
    (hh : haltCost C2.length (exhaustedWidth C2)%1000=976) :
    clockFor C0 C1 C2%1000=105 := by
  unfold clockFor
  omega

theorem exactN_mod_thousand : exactN%1000=105 := by
  rw [exactN_def]
  exact clockFor_mod_thousand seed stage1 stage2 seed_bulk_mod_thousand
    seed_reset_mod_thousand stage1_bulk_mod_thousand stage1_reset_mod_thousand
    stage2_bulk_mod_thousand stage2_halt_mod_thousand

end BeaverStructural.BB6
