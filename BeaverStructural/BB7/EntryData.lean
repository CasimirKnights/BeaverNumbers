import BeaverStructural.BB7.Mid
/-! The zipper of the BB(7) champion from the blank tape after 8574 steps, as a literal. -/

namespace BeaverStructural.BB7

deriving instance DecidableEq for Zip

/-- The zipper at step 8574. -/
def entryZip : Zip := ⟨some .A, [false, false, true, true, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true], [], 108, 8574⟩

/-- The blank-tape run reaches `entryZip` at step 8574 (kernel evaluation). -/
theorem entry_run : Zip.run 8574 ⟨some .A, [], [], 0, 0⟩ = entryZip := by decide +kernel

/-- `entryZip` is B(4; [1]*12) with 0 blanks after the left word and 0 blanks on the right. -/
theorem entry_lists : entryZip.left = bLeft 4 (List.replicate 12 1) ++ List.replicate 0 false ∧
    entryZip.right = List.replicate 0 false := by decide +kernel

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.entry_run
#print axioms BeaverStructural.BB7.entry_lists
