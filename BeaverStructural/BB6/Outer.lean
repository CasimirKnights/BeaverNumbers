import BeaverStructural.BB6.Increment
import BeaverStructural.BB6.Inner
import BeaverStructural.BB6.OuterArithmetic
import BeaverStructural.BB6.Clock

set_option compiler.extract_closed false

namespace BeaverStructural.BB6

/-- Sum of the actual signed head displacements of the original phases. -/
def outerDisplacement (j b : ℕ) : ℤ :=
  ∑ i ∈ Finset.range j, (3*(tower (i+1) b : ℤ)+5)

def outerCost (n b j : ℕ) : ℕ := ∑ i ∈ Finset.range j, phaseCost n b i

theorem outerDisplacement_succ (j b : ℕ) :
    outerDisplacement (j+1) b = outerDisplacement j b+3*tower (j+1) b+5 := by
  simp only [outerDisplacement, Finset.sum_range_succ]
  ring

theorem outerCost_succ (n b j : ℕ) :
    outerCost n b (j+1) = outerCost n b j+phaseCost n b j := by
  exact Finset.sum_range_succ _ _

theorem phaseCost_eq_source (n b j : ℕ) :
    phaseCost n b j =
      (12*widthAfter j b+4*modeAfter j+3*tower (j+1) b+63+12*padicValNat 2 (n-j)) +
        innerCost (2^tower (j+1) b-1) 0 := by
  apply Int.natCast_inj.mp
  rw [Nat.cast_add, phaseCost_from_macro, innerCost_all_ones]
  have ht : tower (j+2) b = 2^tower (j+1) b-1 := rfl
  have hp : 1 ≤ 2^tower (j+1) b := Nat.one_le_pow _ _ (by decide)
  have hc : (tower (j+2) b : ℤ) = (2:ℤ)^tower (j+1) b-1 := by
    rw [ht, Nat.cast_sub hp]
    push_cast
    rfl
  rw [hc]
  push_cast
  ring

/-- One whole positive outer phase, including the inner loop's actual feedback. -/
theorem outer_phase (L n b j : ℕ) (hj : j<n) (hn : n<2^L) (h : ℤ) (c : ℕ) :
    CountedRun table (phaseCost n b j)
      (counterConfig L (n-j) (modeAfter j) (widthAfter j b) 0 (tower (j+1) b) h c)
      (counterConfig L (n-(j+1)) (modeAfter (j+1)) (widthAfter (j+1) b) 0
        (tower (j+2) b) (h+3*tower (j+1) b+5) (c+phaseCost n b j)) := by
  let br := tower (j+1) b
  let a := widthAfter j b
  let m := modeAfter j
  have hn' : n-j < 2^L := lt_of_le_of_lt (Nat.sub_le _ _) hn
  have h₁ := counter_reset_prefix L (n-j) m a br (by omega) hn' (modeAfter_lt j) h c
  have hs : 2^br-1 < 2^(a+br+widthGain m) := by
    have hp : 0 < 2^br := by positivity
    have hle : 2^br ≤ 2^(a+br+widthGain m) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h₂ := counter_inner_all L (n-j-1) (nextMode m) (a+br+widthGain m) (2^br-1) 0 hs
    (h+3*br+5) (c+(12*a+4*m+3*br+63+12*padicValNat 2 (n-j)))
  have ht := h₁.trans h₂
  have hv : n-j-1 = n-(j+1) := by omega
  have hm : nextMode m = modeAfter (j+1) := (modeAfter_succ j).symm
  have ha : a+br+widthGain m = widthAfter (j+1) b := (widthAfter_succ j b).symm
  have hb : 2^br-1 = tower (j+2) b := rfl
  have hc : (12*a+4*m+3*br+63+12*padicValNat 2 (n-j))+innerCost (2^br-1) 0 =
      phaseCost n b j := (phaseCost_eq_source n b j).symm
  have hclock : (c+(12*a+4*m+3*br+63+12*padicValNat 2 (n-j)))+
      innerCost (2^br-1) 0 = c+phaseCost n b j := by
    rw [Nat.add_assoc, hc]
  rw [hv, hm, ha, Nat.zero_add, hclock, hc, hb] at ht
  exact ht

/-- Every successive phase consumes its predecessor's entire written tape. -/
theorem outer_prefix (L n b j : ℕ) (hj : j≤n) (hn : n<2^L) (h : ℤ) (c : ℕ) :
    CountedRun table (outerCost n b j)
      (counterConfig L n 2 b 0 (2^b-1) h c)
      (counterConfig L (n-j) (modeAfter j) (widthAfter j b) 0 (tower (j+1) b)
        (h+outerDisplacement j b) (c+outerCost n b j)) := by
  induction j with
  | zero =>
    simpa [outerCost, outerDisplacement, widthAfter_zero, modeAfter, tower] using
      (CountedRun.refl (δ:=table) (counterConfig L n 2 b 0 (2^b-1) h c))
  | succ j ih =>
    have h₁ := ih (by omega)
    have h₂ := outer_phase L n b j (by omega) hn
      (h+outerDisplacement j b) (c+outerCost n b j)
    have ht := h₁.trans h₂
    simpa only [outerCost_succ, outerDisplacement_succ, add_assoc] using ht

/-- Complete outer exhaustion: exact bulk cost, full tape, head, and no earlier halt. -/
theorem counter_outer_all (L n b : ℕ) (hn : n<2^L) (h : ℤ) (c : ℕ) :
    CountedRun table (bulkCost n b)
      (counterConfig L n 2 b 0 (2^b-1) h c)
      (counterConfig L 0 (phaseMode n) (phaseWidth n b) 0 (tower (n+1) b)
        (h+outerDisplacement n b) (c+bulkCost n b)) := by
  have ht := outer_prefix L n b n le_rfl hn h c
  rw [show outerCost n b n = bulkCost n b by exact (bulkCost_eq_sum_phaseCost n b).symm] at ht
  simpa only [Nat.sub_self, modeAfter, phaseMode, widthAfter, phaseWidth] using ht

end BeaverStructural.BB6
