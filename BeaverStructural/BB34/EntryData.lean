import BeaverStructural.BB34.Machine

/-! The zipper of the BB(3,4) machine from the blank tape after 241 steps, as a literal: B(16, 3, 0) with right
context 2. -/

namespace BeaverStructural.BB34

/-- The zipper at step 241. -/
def entryZip : Zip := ⟨some .A, [.s2, .s2, .s2, .s2, .s2, .s2, .s2, .s2, .s2, .s2, .s2, .s2, .s2, .s2, .s2, .s2, .s3], [.s1, .s1, .s1, .s2], 11, 241⟩

/-- The blank-tape run reaches `entryZip` at step 241 (kernel evaluation). -/
theorem entry_run : Zip.run 241 ⟨some .A, [], [], 0, 0⟩ = entryZip := by decide +kernel

/-- `entryZip` is 2^16 3 to the left and 1^3 2 to the right, with no cell written beyond either. -/
theorem entry_eq : entryZip = ⟨some .A, blk .s2 16 ++ blk .s3 1, blk .s1 3 ++ [.s2], 11, 241⟩ := by
  decide +kernel

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.entry_run
#print axioms BeaverStructural.BB34.entry_eq
