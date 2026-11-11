import BeaverStructural.BB6.TowerModuli

namespace BeaverStructural.BB6.TowerModulus

attribute [local irreducible] tower

def sumCode {m : ℕ} (C : TowerModulus m) (offset nr : ℕ) : ℕ :=
  let k:=C.depth+2
  ((∑ i ∈ Finset.range k, C.residue (offset+i))+
    (nr+k*m-k)*C.steady)%m

def weightedCode {m : ℕ} (C : TowerModulus m) (offset nr : ℕ) : ℕ :=
  let k:=C.depth+2
  let t:=nr+k*m-k
  (2*(∑ i ∈ Finset.range k, (nr+k*m-i)*C.residue (offset+i))+
    t*(t+1)*C.steady)%m

def powerCode {m : ℕ} (C : TowerModulus m) (offset nr power : ℕ) : ℕ :=
  let k:=C.depth+2
  ((∑ i ∈ Finset.range k, (C.residue (offset+i))^power)+
    (nr+k*m-k)*C.steady^power)%m

theorem modulus_positive {m : ℕ} (C : TowerModulus m) : 0<m := by
  cases C with
  | one => decide
  | step _ hm _ _ => exact hm

theorem representative_mod (n m k : ℕ) : n%m=(n%m+k*m)%m := by simp

theorem representative_ge (nr m k : ℕ) (hm : 0<m) : k≤nr+k*m := by
  have h : k≤k*m := by nlinarith
  omega

theorem sumCode_correct {m : ℕ} (C : TowerModulus m) (offset n : ℕ)
    (hn : C.depth+2≤n) :
    (∑ i ∈ Finset.range n, tower (offset+i) 6)%m=C.sumCode offset (n%m) := by
  let k:=C.depth+2
  have hk : k≤n := hn
  have ht : ∀ j, tower (offset+(k+j)) 6%m=C.steady%m := by
    intro j
    rw [C.steady_correct _ (by dsimp only [k]; omega)]
    have hs : C.steady%m=C.steady := by
      rw [← C.steady_correct (C.depth+2) (by omega),Nat.mod_mod]
    exact hs.symm
  have hs := sum_mod_constant_tail (fun i => tower (offset+i) 6) m k (n-k) C.steady ht
  have he : k+(n-k)=n := by omega
  rw [he] at hs
  have hp : (∑ i ∈ Finset.range k, tower (offset+i) 6)%m=
      (∑ i ∈ Finset.range k, C.residue (offset+i))%m := by
    conv_lhs => rw [Finset.sum_nat_mod]
    conv_rhs => rw [Finset.sum_nat_mod]
    apply congrArg (·%m)
    apply Finset.sum_congr rfl
    intro i _
    rw [C.residue_correct,← C.residue_correct,Nat.mod_mod]
  have hd : (n-k)%m=(n%m+k*m-k)%m :=
    Nat.ModEq.sub hk (representative_ge _ _ _ C.modulus_positive)
      (representative_mod n m k) (Nat.ModEq.refl k)
  rw [hs]
  unfold sumCode
  dsimp only
  exact Nat.ModEq.add hp (Nat.ModEq.mul hd (Nat.ModEq.refl C.steady))

theorem powerCode_correct {m : ℕ} (C : TowerModulus m) (offset n power : ℕ)
    (hn : C.depth+2≤n) :
    (∑ i ∈ Finset.range n, (tower (offset+i) 6)^power)%m=C.powerCode offset (n%m) power := by
  let k:=C.depth+2
  have hk : k≤n := hn
  have ht : ∀ j, (tower (offset+(k+j)) 6)^power%m=C.steady^power%m := by
    intro j
    have hs : tower (offset+(k+j)) 6%m=C.steady%m := by
      rw [C.steady_correct _ (by dsimp only [k]; omega)]
      have he : C.steady%m=C.steady := by
        rw [← C.steady_correct (C.depth+2) (by omega),Nat.mod_mod]
      exact he.symm
    exact Nat.ModEq.pow power hs
  have hs := sum_mod_constant_tail (fun i => (tower (offset+i) 6)^power) m k (n-k) (C.steady^power) ht
  have he : k+(n-k)=n := by omega
  rw [he] at hs
  have hp : (∑ i ∈ Finset.range k, (tower (offset+i) 6)^power)%m=
      (∑ i ∈ Finset.range k, (C.residue (offset+i))^power)%m := by
    conv_lhs => rw [Finset.sum_nat_mod]
    conv_rhs => rw [Finset.sum_nat_mod]
    apply congrArg (·%m)
    apply Finset.sum_congr rfl
    intro i _
    have hv : tower (offset+i) 6%m=C.residue (offset+i)%m := by
      rw [← C.residue_correct,Nat.mod_mod]
    exact Nat.ModEq.pow power hv
  have hd : (n-k)%m=(n%m+k*m-k)%m :=
    Nat.ModEq.sub hk (representative_ge _ _ _ C.modulus_positive)
      (representative_mod n m k) (Nat.ModEq.refl k)
  rw [hs]
  unfold powerCode
  dsimp only
  exact Nat.ModEq.add hp (Nat.ModEq.mul hd (Nat.ModEq.refl (C.steady^power)))

theorem weightedCode_correct {m : ℕ} (C : TowerModulus m) (offset n : ℕ)
    (hn : C.depth+2≤n) :
    (2*(∑ i ∈ Finset.range n, (n-i)*tower (offset+i) 6))%m=
      C.weightedCode offset (n%m) := by
  let k:=C.depth+2
  have hk : k≤n := hn
  have ht : ∀ j, tower (offset+(k+j)) 6%m=C.steady%m := by
    intro j
    rw [C.steady_correct _ (by dsimp only [k]; omega)]
    have hs : C.steady%m=C.steady := by
      rw [← C.steady_correct (C.depth+2) (by omega),Nat.mod_mod]
    exact hs.symm
  have hs := twice_weighted_sum_mod_constant_tail (fun i => tower (offset+i) 6)
    m k (n-k) C.steady ht
  have he : k+(n-k)=n := by omega
  rw [he] at hs
  have hrep := representative_mod n m k
  have hrepge := representative_ge (n%m) m k C.modulus_positive
  have hd : (n-k)%m=(n%m+k*m-k)%m := Nat.ModEq.sub hk hrepge hrep (Nat.ModEq.refl k)
  have hp : (∑ i ∈ Finset.range k, (n-i)*tower (offset+i) 6)%m=
      (∑ i ∈ Finset.range k, (n%m+k*m-i)*C.residue (offset+i))%m := by
    conv_lhs => rw [Finset.sum_nat_mod]
    conv_rhs => rw [Finset.sum_nat_mod]
    apply congrArg (·%m)
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i<k := Finset.mem_range.mp hi
    have hv := Nat.ModEq.sub (by omega : i≤n) (by omega : i≤n%m+k*m) hrep (Nat.ModEq.refl i)
    have hval : tower (offset+i) 6%m=C.residue (offset+i)%m := by
      rw [← C.residue_correct,Nat.mod_mod]
    exact Nat.ModEq.mul hv hval
  rw [hs]
  unfold weightedCode
  dsimp only
  exact Nat.ModEq.add (Nat.ModEq.mul (Nat.ModEq.refl 2) hp)
    (Nat.ModEq.mul (Nat.ModEq.mul hd (Nat.ModEq.add hd (Nat.ModEq.refl 1)))
      (Nat.ModEq.refl C.steady))

end BeaverStructural.BB6.TowerModulus
