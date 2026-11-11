import BeaverStructural.BB7b.Machine

/-! The zipper of the BB(7) machine of October 2026 from the blank tape after 3959 steps, as a literal. -/

namespace BeaverStructural.BB7b

deriving instance DecidableEq for Zip

/-- The zipper at step 3959. -/
def entryZip : Zip := ⟨some .E, [], [false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, false, false, false], -55, 3959⟩

/-- The blank-tape run reaches `entryZip` at step 3959 (kernel evaluation). -/
theorem entry_run : Zip.run 3959 ⟨some .A, [], [], 0, 0⟩ = entryZip := by decide +kernel

/-- `entryZip` is K(8; 0, 1^19) with 0 written blanks on the left and 3 on the right. -/
theorem entry_lists : entryZip.left = List.replicate 0 false ∧
    entryZip.right = (kc [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] 8 0 (-55) 3959).right ++
      List.replicate 3 false := by decide +kernel

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.entry_run
#print axioms BeaverStructural.BB7b.entry_lists
