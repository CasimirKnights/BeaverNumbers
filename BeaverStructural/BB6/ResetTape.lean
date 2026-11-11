import BeaverStructural.BB6.ResetWord
import BeaverStructural.BB6.Decrement
import BeaverStructural.BB6.Macros

namespace BeaverStructural.BB6

theorem commonLeft_normal (L a : ℕ) :
    commonLeft L a = [true,false,false,true] ++ (oneBlocks a).reverse ++
      [true,true,true] ++ (oneBlocks (L+1)).reverse ++ [true,true,false,true,true,true] := by
  have hb : writtenJ L ++ terminalBoundary =
      writtenJ (L+1) ++ [true,true,true,false,true,true,true] := by
    rw [← writtenJ_append]
    simp [terminalBoundary, List.append_assoc]
  unfold commonLeft
  rw [List.append_assoc, List.append_assoc, hb, writtenJ_succ a]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [decrement_written a, decrement_written (L+1)]

theorem reset_tape_identification (L a b : ℕ) (h : ℤ) (c : ℕ) :
    atLeft ((counterWord b (2^b-1)).reverse ++ [true,true,false] ++ commonLeft L a)
      (counterRight 0) h c =
    counterZipper (L+a+2) (2^(L+a+2)-2^a-1) 2 b (2^b-1) 0 h c := by
  rw [commonLeft_normal]
  unfold counterZipper counterLeft
  rw [counterWord_reset]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.append_assoc, List.cons_append, List.replicate_succ,
    List.replicate_zero]
  rfl

end BeaverStructural.BB6
