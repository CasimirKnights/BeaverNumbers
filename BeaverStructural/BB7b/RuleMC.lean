import BeaverStructural.BB7b.Machine

/-! MC from the rows of the BB(7) machine of October 2026. -/

namespace BeaverStructural.BB7b

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- MC: the mini-cycle: one cell of the next block is taken and the left block grows by three. -/
theorem rule_MC (n : ℕ) (X : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (2 * n + 10) ⟨some .E, [], false :: (ones (n) ++ (false :: (false :: (true :: X)))), h, c⟩ =
      ⟨some .E, [], false :: (ones (n + 3) ++ (false :: (false :: X))), h + (-2), c + (2 * n + 10)⟩ := by
  have s0 : ∀ (h : ℤ) (c : ℕ), Zip.run 3 ⟨some .E, [], false :: (ones (n) ++ (false :: (false :: (true :: X)))), h, c⟩ =
      ⟨some .B, true :: (true :: []), ones (n) ++ (false :: (false :: (true :: X))), h + (1), c + 3⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s1 := fun (h : ℤ) (c : ℕ) => crossB (n) (true :: (true :: [])) (false :: (false :: (true :: X))) h c
  have s2 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (n + 2) ++ [], false :: (false :: (true :: X)), h, c⟩ =
      ⟨some .E, ones (n + 2) ++ [], true :: (false :: (false :: X)), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s3 := fun (h : ℤ) (c : ℕ) => crossE (n + 2) ([]) (false :: (false :: X)) h c
  have s4 : ∀ (h : ℤ) (c : ℕ), Zip.run 1 ⟨some .E, [], ones (n + 3) ++ (false :: (false :: X)), h, c⟩ =
      ⟨some .E, [], false :: (ones (n + 3) ++ (false :: (false :: X))), h + (-1), c + 1⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have e0 := s0 h c
  have e1 := chainB e0 (s1 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e2 := chainB e1 (s2 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e3 := chainB e2 (s3 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e4 := chainB e3 (s4 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  refine (congrArg (fun t => Zip.run t _) (show (2 * n + 10) = 3 + (n) + 4 + (n + 2) + 1 by ring)).trans (e4.trans ?_)
  exact zip_eq rfl (by simp) (by simp) (by push_cast; ring) (by ring)

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.rule_MC
