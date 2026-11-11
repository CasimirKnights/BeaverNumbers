import BeaverStructural.BB6.CounterTape
import BeaverStructural.BB6.Strips

namespace BeaverStructural.BB6

theorem decrement_bridge (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run 4 (atLeft (false::false::true::l) (false::r) h c) =
      ⟨some .C, true::true::true::true::l, r, h+2, c+4⟩ := by
  simp [atLeft, Zipper.run, Zipper.step, table]
  omega

/-- Original Q^(3k) U J^k row word, retaining arbitrary exterior tape. -/
theorem decrement_strip (k : ℕ) (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run (12*k+4)
      (atLeft (List.replicate (3*k) true ++ false::false::true::l) (false::r) h c) =
      ⟨some .C, writtenJ k ++ true::true::true::true::l, r, h+2, c+12*k+4⟩ := by
  rw [show 12*k+4 = 3*(3*k)+4+3*k by omega,
    Zipper.run_add, Zipper.run_add, q_boundary_strip, decrement_bridge, j_strip]
  congr 1 <;> push_cast <;> omega

theorem decrement_written (k : ℕ) (l : List Bool) :
    writtenJ k ++ true::l = true::((oneBlocks k).reverse ++ l) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [writtenJ_succ, oneBlocks_succ, List.reverse_append]
    simp only [List.append_assoc, List.cons_append, List.nil_append, ih]
    rfl

/-- Counter-level original decrement, with the unchanged prefix physically
present on the tape and both zero and nonzero exterior contexts retained. -/
theorem counter_decrement (L v : ℕ) (hv : 0 < v) (hL : v < 2^L)
    (left right : List Bool) (head : ℤ) (clock : ℕ) :
    Zipper.run (12*padicValNat 2 v+4)
      (atLeft ((counterWord L v).reverse ++ left) (false::right) head clock) =
      ⟨some .C, true::((counterWord L (v-1)).reverse ++ left),
        right, head+2, clock+12*padicValNat 2 v+4⟩ := by
  obtain ⟨before, after⟩ := counterWord_decrement L v hv hL
  rw [before, after]
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_assoc, List.cons_append]
  rw [decrement_strip]
  congr 1
  exact decrement_written _ _

end BeaverStructural.BB6
