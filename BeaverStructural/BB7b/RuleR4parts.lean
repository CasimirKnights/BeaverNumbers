import BeaverStructural.BB7b.Machine

/-! FWZ0, FWZ, END2, BW, R4fin from the rows of the BB(7) machine of October 2026. -/

namespace BeaverStructural.BB7b

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- FWZ0: the first forward pass into the blank tape: the block loses one cell and leaves 0 1 behind. -/
theorem rule_FWZ0 (n : ℕ) (L : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (2 * n + 8) ⟨some .F, L, false :: (ones (n + 2) ++ []), h, c⟩ =
      ⟨some .F, false :: (true :: L), false :: (ones (n + 1) ++ (false :: (false :: []))), h + (2), c + (2 * n + 8)⟩ := by
  have s0 : ∀ (h : ℤ) (c : ℕ), Zip.run 3 ⟨some .F, L, false :: (ones (n + 2) ++ []), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: L)), ones (n) ++ [], h + (3), c + 3⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s1 := fun (h : ℤ) (c : ℕ) => crossB (n) (false :: (false :: (true :: L))) ([]) h c
  have s2 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (n) ++ (false :: (false :: (true :: L))), [], h, c⟩ =
      ⟨some .F, ones (n) ++ (false :: (false :: (true :: L))), true :: (false :: (false :: [])), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s3 := fun (h : ℤ) (c : ℕ) => crossF (n) (false :: (false :: (true :: L))) (false :: (false :: [])) h c
  have s4 : ∀ (h : ℤ) (c : ℕ), Zip.run 1 ⟨some .F, false :: (false :: (true :: L)), ones (n + 1) ++ (false :: (false :: [])), h, c⟩ =
      ⟨some .F, false :: (true :: L), false :: (ones (n + 1) ++ (false :: (false :: []))), h + (-1), c + 1⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have e0 := s0 h c
  have e1 := chainB e0 (s1 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e2 := chainB e1 (s2 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e3 := chainB e2 (s3 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e4 := chainB e3 (s4 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  refine (congrArg (fun t => Zip.run t _) (show (2 * n + 8) = 3 + (n) + 4 + (n) + 1 by ring)).trans (e4.trans ?_)
  exact zip_eq rfl (by simp) (by simp) (by push_cast; ring) (by ring)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- FWZ: one forward pass into the blank tape, two written blanks behind the block: the block loses one cell and leaves 0 1 behind. -/
theorem rule_FWZ (n : ℕ) (L : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (2 * n + 8) ⟨some .F, L, false :: (ones (n + 2) ++ (false :: (false :: []))), h, c⟩ =
      ⟨some .F, false :: (true :: L), false :: (ones (n + 1) ++ (false :: (false :: []))), h + (2), c + (2 * n + 8)⟩ := by
  have s0 : ∀ (h : ℤ) (c : ℕ), Zip.run 3 ⟨some .F, L, false :: (ones (n + 2) ++ (false :: (false :: []))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: L)), ones (n) ++ (false :: (false :: [])), h + (3), c + 3⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s1 := fun (h : ℤ) (c : ℕ) => crossB (n) (false :: (false :: (true :: L))) (false :: (false :: [])) h c
  have s2 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (n) ++ (false :: (false :: (true :: L))), false :: (false :: []), h, c⟩ =
      ⟨some .F, ones (n) ++ (false :: (false :: (true :: L))), true :: (false :: (false :: [])), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s3 := fun (h : ℤ) (c : ℕ) => crossF (n) (false :: (false :: (true :: L))) (false :: (false :: [])) h c
  have s4 : ∀ (h : ℤ) (c : ℕ), Zip.run 1 ⟨some .F, false :: (false :: (true :: L)), ones (n + 1) ++ (false :: (false :: [])), h, c⟩ =
      ⟨some .F, false :: (true :: L), false :: (ones (n + 1) ++ (false :: (false :: []))), h + (-1), c + 1⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have e0 := s0 h c
  have e1 := chainB e0 (s1 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e2 := chainB e1 (s2 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e3 := chainB e2 (s3 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e4 := chainB e3 (s4 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  refine (congrArg (fun t => Zip.run t _) (show (2 * n + 8) = 3 + (n) + 4 + (n) + 1 by ring)).trans (e4.trans ?_)
  exact zip_eq rfl (by simp) (by simp) (by push_cast; ring) (by ring)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- END2: the last forward pass: the block of one cell. -/
theorem rule_END2 (x : Bool) (L : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (9) ⟨some .F, false :: (true :: (x :: L)), false :: (true :: (false :: (false :: []))), h, c⟩ =
      ⟨some .F, L, x :: (true :: (false :: (true :: (false :: (false :: (false :: [])))))), h + (-3), c + (9)⟩ := by
  have s0 : ∀ (h : ℤ) (c : ℕ), Zip.run 9 ⟨some .F, false :: (true :: (x :: L)), false :: (true :: (false :: (false :: []))), h, c⟩ =
      ⟨some .F, L, x :: (true :: (false :: (true :: (false :: (false :: (false :: [])))))), h + (-3), c + 9⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have e0 := s0 h c
  refine (congrArg (fun t => Zip.run t _) (show (9) = 9 by ring)).trans (e0.trans ?_)
  exact zip_eq rfl (by simp) (by simp) (by push_cast; ring) (by ring)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- BW: one backward pass: two trail pairs 0 1 0 1 become one digit 1 1 0 0. -/
theorem rule_BW (x : Bool) (L X : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (10) ⟨some .F, true :: (false :: (true :: (x :: L))), false :: (true :: (false :: X)), h, c⟩ =
      ⟨some .F, L, x :: (true :: (false :: (true :: (true :: (false :: (false :: X)))))), h + (-4), c + (10)⟩ := by
  have s0 : ∀ (h : ℤ) (c : ℕ), Zip.run 10 ⟨some .F, true :: (false :: (true :: (x :: L))), false :: (true :: (false :: X)), h, c⟩ =
      ⟨some .F, L, x :: (true :: (false :: (true :: (true :: (false :: (false :: X)))))), h + (-4), c + 10⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have e0 := s0 h c
  refine (congrArg (fun t => Zip.run t _) (show (10) = 10 by ring)).trans (e0.trans ?_)
  exact zip_eq rfl (by simp) (by simp) (by push_cast; ring) (by ring)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- R4fin: the end of the backward passes: state C on a 1, the halting row. -/
theorem rule_R4fin (L X : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (6) ⟨some .F, false :: L, true :: (true :: (false :: (true :: X))), h, c⟩ =
      ⟨none, true :: (true :: (false :: (false :: (true :: L)))), X, h + (4), c + (6)⟩ := by
  have s0 : ∀ (h : ℤ) (c : ℕ), Zip.run 6 ⟨some .F, false :: L, true :: (true :: (false :: (true :: X))), h, c⟩ =
      ⟨none, true :: (true :: (false :: (false :: (true :: L)))), X, h + (4), c + 6⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have e0 := s0 h c
  refine (congrArg (fun t => Zip.run t _) (show (6) = 6 by ring)).trans (e0.trans ?_)
  exact zip_eq rfl (by simp) (by simp) (by push_cast; ring) (by ring)

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.rule_FWZ0
#print axioms BeaverStructural.BB7b.rule_FWZ
#print axioms BeaverStructural.BB7b.rule_END2
#print axioms BeaverStructural.BB7b.rule_BW
#print axioms BeaverStructural.BB7b.rule_R4fin
