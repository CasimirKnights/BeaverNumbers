import BeaverStructural.BB6.DecimalModulus200
import BeaverStructural.BB6.TowerResidueSums
import BeaverStructural.BB6.StageTowerResidues

namespace BeaverStructural.BB6.Decimal200

set_option compiler.extract_closed false
attribute [local irreducible] tower towerSum exhaustedWidth exhaustedRight
  resetCounter stage1 stage2

theorem modEq_of_residue {m n r : ℕ} (h : n%m=r) : Nat.ModEq m n r := by
  unfold Nat.ModEq
  rw [← h,Nat.mod_mod]

def seedWidthCode {m : ℕ} (C : TowerModulus m) : ℕ :=
  ((∑ i ∈ Finset.range 8, C.residue i)+12)%m

def powCode {m p : ℕ} (C : TowerModulus p) (nr : ℕ) : ℕ :=
  modularPower 2 (nr+200*p) m

theorem prefix_correct {m : ℕ} (C : TowerModulus m) (n : ℕ) :
    towerSum n 6%m=(∑ i ∈ Finset.range n,C.residue i)%m := by
  unfold towerSum
  conv_lhs => rw [Finset.sum_nat_mod]
  conv_rhs => rw [Finset.sum_nat_mod]
  apply congrArg (·%m)
  apply Finset.sum_congr rfl
  intro i _
  rw [C.residue_correct,← C.residue_correct,Nat.mod_mod]

theorem width_seed_shape_of (C : Counter) (b : ℕ) (hC : C=⟨3,7,b⟩) :
    exhaustedWidth C=towerSum 8 b+12 := by rw [hC,width_seed_shape]

theorem seedWidthCode_correct {m : ℕ} (C : TowerModulus m) :
    exhaustedWidth seed%m=seedWidthCode C := by
  rw [width_seed_shape_of seed 6 rfl]
  unfold seedWidthCode
  exact Nat.ModEq.add (prefix_correct C 8) (Nat.ModEq.refl 12)

#check seedWidthCode_correct

theorem tower_le_width (C : Counter) (i : ℕ) (hi : i≤C.count) :
    tower i C.base≤exhaustedWidth C := by
  have hs : tower i C.base≤towerSum (C.count+1) C.base := by
    unfold towerSum
    exact Finset.single_le_sum (f:=fun j => tower j C.base) (s:=Finset.range (C.count+1))
      (a:=i) (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  unfold exhaustedWidth
  omega

theorem seedWidth_large : 200≤exhaustedWidth seed :=
  TowerModulus.tower_two_large.trans (tower_le_width seed 2 (by decide))

#check seedWidth_large

theorem powCode_correct {m p : ℕ} (C : TowerModulus p)
    (period : modularPower 2 (200+p) m=modularPower 2 200 m)
    (n nr : ℕ) (hn : 200≤n) (hr : n%p=nr) :
    2^n%m=powCode (m:=m) C nr := by
  have hp := C.modulus_positive
  have hrb : 200≤nr+200*p := by omega
  have hrr : nr%p=nr := by rw [← hr,Nat.mod_mod]
  have he : n%p=(nr+200*p)%p := by simp [hr,Nat.add_mod,Nat.mul_mod,hrr]
  have hper : 2^(200+p)%m=2^200%m := by simpa only [modularPower_eq] using period
  rw [powCode,modularPower_eq]
  exact pow2_mod_of_congruent m 200 p n (nr+200*p) hn hrb hper he


#check powCode_correct

theorem predecessor_mod (n m : ℕ) (hn : 0<n) (hm : 0<m) :
    (n-1)%m=(n%m+m-1)%m := by
  have he : n%m=(n%m+m)%m := by simp
  exact Nat.ModEq.sub hn (by omega) he (Nat.ModEq.refl 1)

theorem reset_count_31 (C : Counter) (hL : C.length=3) :
    (resetCounter C).count=31*2^exhaustedWidth C-1 := by
  rw [resetCounter_count,hL]
  norm_num only [Nat.reduceAdd,Nat.reducePow,Nat.reduceSub]

theorem stage1_count_formula : stage1.count=31*2^exhaustedWidth seed-1 := by
  rewrite [stage1]
  exact reset_count_31 seed rfl

def count1Code {m p : ℕ} (C : TowerModulus p) : ℕ :=
  (31*powCode (m:=m) C (seedWidthCode C)+m-1)%m

#check stage1_count_formula

theorem count1_modular {m p : ℕ} (C : TowerModulus p) (hm : 0<m)
    (period : modularPower 2 (200+p) m=modularPower 2 200 m)
    (a ar : ℕ) (ha : 200≤a) (har : a%p=ar) :
    (31*2^a-1)%m=(31*powCode (m:=m) C ar+m-1)%m := by
  have he := powCode_correct (m:=m) C period a ar ha har
  have hn : 0<31*2^a := by positivity
  have he' : Nat.ModEq m (2^a) (powCode (m:=m) C ar) := modEq_of_residue he
  have hh : Nat.ModEq m (31*2^a) (31*powCode (m:=m) C ar+m) := by
    simpa only [Nat.ModEq,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod] using
      Nat.ModEq.mul (Nat.ModEq.refl 31) he'
  have hrr : 0<31*powCode (m:=m) C ar+m := by omega
  exact Nat.ModEq.sub hn hrr hh (Nat.ModEq.refl 1)

theorem count1Code_correct {m p : ℕ} (C : TowerModulus p) (hm : 0<m)
    (period : modularPower 2 (200+p) m=modularPower 2 200 m) :
    stage1.count%m=count1Code (m:=m) C := by
  rw [stage1_count_formula]
  exact count1_modular C hm period (exhaustedWidth seed) (seedWidthCode C)
    seedWidth_large (seedWidthCode_correct C)

#check count1Code_correct

theorem stage1_sum_code {m : ℕ} (C : TowerModulus m) (n : ℕ)
    (hn : C.depth+2≤n) : towerSum n stage1.base%m=C.sumCode 8 (n%m) := by
  unfold towerSum
  simp_rw [tower_stage1,Nat.add_comm _ 8]
  exact C.sumCode_correct 8 n hn

#check stage1_sum_code

def width1Code {m p : ℕ} (C : TowerModulus m) (P : TowerModulus p) : ℕ :=
  (C.sumCode 8 ((count1Code (m:=m) P+1)%m)+
    5*(count1Code (m:=3*m) P/3)+2)%m

theorem width_from_sum (K : Counter) (m sr qr : ℕ)
    (hs : towerSum (K.count+1) K.base%m=sr) (hq : (K.count/3)%m=qr)
    (hr : K.count%3=1) : exhaustedWidth K%m=(sr+5*qr+2)%m := by
  unfold exhaustedWidth
  rw [if_pos hr]
  exact Nat.ModEq.add (Nat.ModEq.add (modEq_of_residue hs)
    (Nat.ModEq.mul (Nat.ModEq.refl 5) (modEq_of_residue hq))) (Nat.ModEq.refl 2)

theorem width1Code_correct {m p : ℕ} (C : TowerModulus m) (P : TowerModulus p)
    (period : modularPower 2 (200+p) m=modularPower 2 200 m)
    (period3 : modularPower 2 (200+p) (3*m)=modularPower 2 200 (3*m))
    (hdepth : C.depth+2≤stage1.count+1) :
    exhaustedWidth stage1%m=width1Code C P := by
  have hm := C.modulus_positive
  have hn := count1Code_correct P hm period
  have hn3 := count1Code_correct P (by omega : 0<3*m) period3
  have hq : (stage1.count/3)%m=count1Code (m:=3*m) P/3 := by
    rw [← Nat.mod_mul_right_div_self,hn3]
  have hs := stage1_sum_code C (stage1.count+1) hdepth
  have hn' : Nat.ModEq m stage1.count (count1Code (m:=m) P) := modEq_of_residue hn
  have hnr : (stage1.count+1)%m=(count1Code (m:=m) P+1)%m :=
    Nat.ModEq.add hn' (Nat.ModEq.refl 1)
  rw [hnr] at hs
  exact width_from_sum stage1 m _ _ hs hq stage1_residue


theorem reset_length_plus_two_mod (K : Counter) (m ar : ℕ)
    (hL : K.length=3) (ha : exhaustedWidth K%m=ar) :
    ((resetCounter K).length+2)%m=(ar+7)%m := by
  rw [resetCounter_length,hL]
  have he : 3+exhaustedWidth K+2+2=exhaustedWidth K+7 := by omega
  rw [he]
  exact Nat.ModEq.add (modEq_of_residue ha) (Nat.ModEq.refl 7)

theorem length1_plus_two_code {m : ℕ} (C : TowerModulus m) :
    (stage1.length+2)%m=(seedWidthCode C+7)%m := by
  rw [stage1]
  exact reset_length_plus_two_mod seed m _ rfl (seedWidthCode_correct C)

theorem length1_large : 200≤stage1.length+2 := by
  have := stage1_length_mod_thousand
  omega

theorem width1_large : 200≤exhaustedWidth stage1 := by
  have := stage1_width_mod_thousand
  omega

def count2Code {m p q : ℕ} (P : TowerModulus p) (Q : TowerModulus q) : ℕ :=
  let lpow:=powCode (m:=m) P ((seedWidthCode P+7)%p)
  let apow:=powCode (m:=m) P (width1Code P Q)
  (((lpow+m-1)%m)*apow+m-1)%m

theorem reset_count_modular (L a m lp ap : ℕ) (hm : 0<m)
    (hl : 2^(L+2)%m=lp) (ha : 2^a%m=ap) :
    ((2^(L+2)-1)*2^a-1)%m=(((lp+m-1)%m)*ap+m-1)%m := by
  have hpow : 0<(2:ℕ)^(L+2) := by positivity
  have hfac : 0<2^(L+2)-1 := by have := self_lt_two_pow (L+2); omega
  have hprod : 0<(2^(L+2)-1)*2^a := by positivity
  have hf : (2^(L+2)-1)%m=(lp+m-1)%m := by rw [predecessor_mod _ _ hpow hm,hl]
  have hp : ((2^(L+2)-1)*2^a)%m=(((lp+m-1)%m)*ap)%m :=
    Nat.ModEq.mul (modEq_of_residue hf) (modEq_of_residue ha)
  rw [predecessor_mod _ _ hprod hm,hp]
  have he : Nat.ModEq m ((((lp+m-1)%m)*ap)%m+m) (((lp+m-1)%m)*ap+m) := by
    unfold Nat.ModEq
    simp
  exact Nat.ModEq.sub (by omega) (by omega) he (Nat.ModEq.refl 1)

theorem count2Code_correct {m p q : ℕ} (P : TowerModulus p) (Q : TowerModulus q)
    (hm : 0<m)
    (period : modularPower 2 (200+p) m=modularPower 2 200 m)
    (periodP : modularPower 2 (200+q) p=modularPower 2 200 p)
    (periodP3 : modularPower 2 (200+q) (3*p)=modularPower 2 200 (3*p))
    (hdepth : P.depth+2≤stage1.count+1) : stage2.count%m=count2Code (m:=m) P Q := by
  have hl := powCode_correct (m:=m) P period (stage1.length+2)
    ((seedWidthCode P+7)%p) length1_large (length1_plus_two_code P)
  have ha := powCode_correct (m:=m) P period (exhaustedWidth stage1)
    (width1Code P Q) width1_large (width1Code_correct P Q periodP periodP3 hdepth)
  rw [stage2,resetCounter_count]
  exact reset_count_modular stage1.length (exhaustedWidth stage1) m _ _ hm hl ha

end BeaverStructural.BB6.Decimal200
