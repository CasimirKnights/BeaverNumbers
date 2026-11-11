import BeaverStructural.BB6.ResetTape
import BeaverStructural.BB6.Inner
import BeaverStructural.BB6.Clock

namespace BeaverStructural.BB6

/-- Complete mode-one rebuilding before its new inner counter settles. -/
theorem zero_outer_reset_prefix (L a b : ℕ) (h : ℤ) (c : ℕ) :
    CountedRun table (12*L+12*a+3*b+97) (counterConfig L 0 1 a 0 b h c)
      (counterConfig (L+a+2) (2^(L+a+2)-2^a-1) 2 b (2^b-1) 0
        (h+3*b+5) (c+12*L+12*a+3*b+97)) := by
  apply CountedRun.of_active_endpoint
  · rw [counterConfig, ← Zipper.run_config]
    rw [show 12*L+12*a+3*b+97 = (12*L+12*a+3*1+56)+(3*b+38) by omega,
      Zipper.run_add, zero_outer_common L 1 a b h c]
    change ((Zipper.mk (some .C) (commonLeft L a)
      ([true,true,false,false] ++ List.replicate (3*(b+1)) true)
      (h-1+4) (c+12*L+12*a+3*1+56)).run (3*b+38)).config = _
    rw [reset_tail, reset_tape_identification]
    congr 2 <;> push_cast <;> omega
  · simp [counterConfig, counterZipper, Zipper.config]

theorem resetCost_eq_prefix_inner (L a b : ℕ) :
    resetCost L a b = (12*L+12*a+3*b+97)+innerCost (2^b-1) 0 := by
  apply Int.natCast_inj.mp
  rw [Nat.cast_add, resetCost_counted_polynomial, innerCost_all_ones]
  push_cast
  ring

/-- Full zero-outer reset with read-after-write inner settling and exact clock. -/
theorem zero_outer_reset (L a b : ℕ) (h : ℤ) (c : ℕ) :
    CountedRun table (resetCost L a b) (counterConfig L 0 1 a 0 b h c)
      (counterConfig (L+a+2) (2^(L+a+2)-2^a-1) 2 b 0 (2^b-1)
        (h+3*b+5) (c+resetCost L a b)) := by
  have hp : 0 < 2^b := by positivity
  have h₁ := zero_outer_reset_prefix L a b h c
  have h₂ := counter_inner_all (L+a+2) (2^(L+a+2)-2^a-1) 2 b (2^b-1) 0
    (by omega) (h+3*b+5) (c+12*L+12*a+3*b+97)
  have ht := h₁.trans h₂
  simpa only [resetCost_eq_prefix_inner, Nat.zero_add, Nat.add_assoc] using ht

/-- The final physical tape from the original leftmost one, in reading order. -/
def terminalPhysicalWord (L a b : ℕ) : List Bool :=
  [true,true,true,false,true,true] ++ oneBlocks (L+1) ++ [true,true,true] ++
    oneBlocks (a+1) ++ [true,false] ++ List.replicate (3*b+5) true

/-- The full terminal zipper agrees with the documented original physical word,
not merely its symbol count or a finite observation window. -/
theorem terminal_full_word (L a b : ℕ) (h : ℤ) (c : ℕ) :
    (terminalZipper L a b h c).left.reverse ++ (terminalZipper L a b h c).right =
      terminalPhysicalWord L a b := by
  simp only [terminalZipper, List.reverse_append, commonLeft_normal,
    List.reverse_reverse, List.reverse_cons, List.reverse_nil, List.nil_append]
  unfold terminalPhysicalWord
  rw [oneBlocks_succ a, show 3*b+5 = 3+(3*b+2) by omega, List.replicate_add]
  simp only [List.replicate_add, List.append_assoc, List.cons_append, List.nil_append, List.replicate_succ,
    List.replicate_zero]
  simp only [replicate_append_cons, List.append_nil]

end BeaverStructural.BB6
