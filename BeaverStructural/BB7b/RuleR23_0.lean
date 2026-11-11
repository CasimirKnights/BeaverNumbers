import BeaverStructural.BB7b.Machine

/-! R23_0 from the rows of the BB(7) machine of October 2026. -/

namespace BeaverStructural.BB7b

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- R23_0: 0 zero digits then a nonzero digit, with counter b = n + 0: the sweep, the turn and the return. -/
theorem rule_R23_0 (n : ℕ) (X : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (16 * n + 58) ⟨some .E, [], false :: (ones (2 * (n + 0) + 1) ++ (false :: (false :: (false :: (false :: (true :: (true :: X))))))), h, c⟩ =
      ⟨some .E, [], false :: (true :: (false :: (false :: (ones (2 * (n + 3)) ++ (false :: (false :: X)))))), h + (-4), c + (16 * n + 58)⟩ := by
  rw [show 2 * (n + 0) + 1 = 2 * n + 1 by ring, show 2 * (n + 3) = 2 * n + 6 by ring]
  have s0 : ∀ (h : ℤ) (c : ℕ), Zip.run 3 ⟨some .E, [], false :: (ones (2 * n + 1) ++ (false :: (false :: (false :: (false :: (true :: (true :: X))))))), h, c⟩ =
      ⟨some .B, true :: (true :: []), ones (2 * n + 1) ++ (false :: (false :: (false :: (false :: (true :: (true :: X)))))), h + (1), c + 3⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s1 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 1) (true :: (true :: [])) (false :: (false :: (false :: (false :: (true :: (true :: X)))))) h c
  have s2 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 3) ++ [], false :: (false :: (false :: (false :: (true :: (true :: X))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 3) ++ [], true :: (false :: (false :: (false :: (true :: (true :: X))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s3 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 3) ([]) (false :: (false :: (false :: (true :: (true :: X))))) h c
  have s4 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, [], ones (2 * n + 4) ++ (false :: (false :: (false :: (true :: (true :: X))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: [])), ones (2 * n + 2) ++ (false :: (false :: (false :: (true :: (true :: X))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s5 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 2) (false :: (false :: (true :: []))) (false :: (false :: (false :: (true :: (true :: X))))) h c
  have s6 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 2) ++ (false :: (false :: (true :: []))), false :: (false :: (false :: (true :: (true :: X)))), h, c⟩ =
      ⟨some .F, ones (2 * n + 2) ++ (false :: (false :: (true :: []))), true :: (false :: (false :: (true :: (true :: X)))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s7 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 2) (false :: (false :: (true :: []))) (false :: (false :: (true :: (true :: X)))) h c
  have s8 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: [])), ones (2 * n + 3) ++ (false :: (false :: (true :: (true :: X)))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: [])))), ones (2 * n + 1) ++ (false :: (false :: (true :: (true :: X)))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s9 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 1) (false :: (false :: (true :: (false :: (true :: []))))) (false :: (false :: (true :: (true :: X)))) h c
  have s10 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 1) ++ (false :: (false :: (true :: (false :: (true :: []))))), false :: (false :: (true :: (true :: X))), h, c⟩ =
      ⟨some .E, ones (2 * n + 1) ++ (false :: (false :: (true :: (false :: (true :: []))))), true :: (false :: (false :: (true :: X))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s11 := fun (h : ℤ) (c : ℕ) => crossE (2 * n + 1) (false :: (false :: (true :: (false :: (true :: []))))) (false :: (false :: (true :: X))) h c
  have s12 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .E, false :: (false :: (true :: (false :: (true :: [])))), ones (2 * n + 2) ++ (false :: (false :: (true :: X))), h, c⟩ =
      ⟨some .B, true :: (true :: (true :: (false :: (true :: [])))), ones (2 * n + 2) ++ (false :: (false :: (true :: X))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s13 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 2) (true :: (true :: (true :: (false :: (true :: []))))) (false :: (false :: (true :: X))) h c
  have s14 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 5) ++ (false :: (true :: [])), false :: (false :: (true :: X)), h, c⟩ =
      ⟨some .E, ones (2 * n + 5) ++ (false :: (true :: [])), true :: (false :: (false :: X)), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s15 := fun (h : ℤ) (c : ℕ) => crossE (2 * n + 5) (false :: (true :: [])) (false :: (false :: X)) h c
  have s16 : ∀ (h : ℤ) (c : ℕ), Zip.run 10 ⟨some .E, false :: (true :: []), ones (2 * n + 6) ++ (false :: (false :: X)), h, c⟩ =
      ⟨some .E, [], false :: (true :: (false :: (false :: (ones (2 * n + 6) ++ (false :: (false :: X)))))), h + (-4), c + 10⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have e0 := s0 h c
  have e1 := chainB e0 (s1 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e2 := chainB e1 (s2 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e3 := chainB e2 (s3 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e4 := chainB e3 (s4 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e5 := chainB e4 (s5 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e6 := chainB e5 (s6 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e7 := chainB e6 (s7 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e8 := chainB e7 (s8 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e9 := chainB e8 (s9 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e10 := chainB e9 (s10 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e11 := chainB e10 (s11 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e12 := chainB e11 (s12 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e13 := chainB e12 (s13 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e14 := chainB e13 (s14 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e15 := chainB e14 (s15 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e16 := chainB e15 (s16 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  refine (congrArg (fun t => Zip.run t _) (show (16 * n + 58) = 3 + (2 * n + 1) + 4 + (2 * n + 3) + 4 + (2 * n + 2) + 4 + (2 * n + 2) + 4 + (2 * n + 1) + 4 + (2 * n + 1) + 4 + (2 * n + 2) + 4 + (2 * n + 5) + 10 by ring)).trans (e16.trans ?_)
  exact zip_eq rfl (by simp) (by simp) (by push_cast; ring) (by ring)

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.rule_R23_0
