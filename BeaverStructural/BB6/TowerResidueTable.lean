import BeaverStructural.BB6.TowerResidueSums

namespace BeaverStructural.BB6.TowerModulus
attribute [local irreducible] tower
set_option maxHeartbeats 200000

/-- Complete finite prefix including its first provably stable value. -/
def residuePrefix {m : ℕ} (C : TowerModulus m) : List ℕ :=
  List.ofFn (fun i : Fin (C.depth+3) => C.residue i)

def nextRow (m p : ℕ) (xs : List ℕ) : List ℕ :=
  [6%m,63%m,9223372036854775807%m] ++
    (xs.drop 2).map (fun v => (modularPower 2 (v+200*p) m+m-1)%m)

@[simp] theorem prefix_length {m : ℕ} (C : TowerModulus m) :
    C.residuePrefix.length=C.depth+3 := by simp [residuePrefix]

@[simp] theorem prefix_getElem {m : ℕ} (C : TowerModulus m) (i : ℕ)
    (hi : i<C.residuePrefix.length) : C.residuePrefix[i]=C.residue i := by
  unfold residuePrefix
  rw [List.getElem_ofFn]

theorem prefix_one : TowerModulus.one.residuePrefix=[0,0,0] := rfl

theorem prefix_step {m p : ℕ} (C : TowerModulus p) (hm : 0<m) (hp : 0<p)
    (period : modularPower 2 (200+p) m=modularPower 2 200 m) :
    (TowerModulus.step C hm hp period).residuePrefix=nextRow m p C.residuePrefix := by
  apply List.ext_getElem
  · simp [nextRow, depth]
  · intro i hi hj
    rw [prefix_getElem]
    by_cases h0 : i=0
    · subst i; simp [nextRow,residue]
    by_cases h1 : i=1
    · subst i; simp [nextRow,residue]
    by_cases h2 : i=2
    · subst i; simp [nextRow,residue]
    have h3 : 3 ≤ i := by omega
    unfold nextRow
    rw [List.getElem_append_right (by simp only [List.length_cons,List.length_nil]; omega)]
    simp only [List.length_cons,List.length_nil,List.getElem_map,List.getElem_drop]
    rw [prefix_getElem]
    simp only [residue,if_neg h0,if_neg h1,if_neg h2]
    rw [show 2 + (i - (0+1+1+1)) = i-1 by omega]

end BeaverStructural.BB6.TowerModulus
