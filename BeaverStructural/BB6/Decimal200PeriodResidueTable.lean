import BeaverStructural.BB6.Decimal200PeriodRows9
namespace BeaverStructural.BB6.Decimal200
set_option compiler.extract_closed false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem period_depth_numeric : chain199.depth=200 := by decide +kernel

def periodResidueValue (h : ℕ) : ℕ :=
  if hh : h<periodRow199.length then periodRow199[h] else 28951261664237217368977054993024337984022230380872240937097767535559243296246647670661132583041468249306282457279721797579758707070357673727

private theorem residue_from_prefix {m : ℕ} (C : TowerModulus m) (xs : List ℕ)
    (hc : C.residuePrefix=xs) (h : ℕ) (hh : h<xs.length) :
    C.residue h=xs[h] := by
  have hp : h<C.residuePrefix.length := by rw [hc]; exact hh
  have he := C.prefix_getElem h hp
  simpa only [hc] using he.symm

theorem periodResidueValue_correct (h : ℕ) : chain199.residue h=periodResidueValue h := by
  unfold periodResidueValue
  split_ifs with hh
  · exact residue_from_prefix chain199 periodRow199 periodRow199_correct h hh
  · have hl : periodRow199.length=203 := by decide +kernel
    have hd : chain199.depth+2≤h := by rewrite [period_depth_numeric]; omega
    exact (chain199.residue_correct h).symm.trans
      ((chain199.steady_correct h hd).trans period_steady_code)

theorem period_prefix8_sum :
    (∑ i ∈ Finset.range (chain199.depth+2), chain199.residue (8+i))=5105966054849944097358373129091911437281600430082716805509604042201712308207700511569031009344100933015631897735316787520389272657935468530354 := by
  rewrite [period_depth_numeric]
  have he : (∑ i ∈ Finset.range 202, chain199.residue (8+i))=
      (∑ i ∈ Finset.range 202, periodResidueValue (8+i)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact periodResidueValue_correct (8+i)
  exact he.trans (by decide +kernel)

end BeaverStructural.BB6.Decimal200
