import BeaverStructural.BB7b.Machine

/-! R23_6 from the rows of the BB(7) machine of October 2026. -/

namespace BeaverStructural.BB7b

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- R23_6: 6 zero digits then a nonzero digit, with counter b = n + 6: the sweep, the turn and the return. -/
theorem rule_R23_6 (n : ℕ) (X : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (64 * n + 442) ⟨some .E, [], false :: (ones (2 * (n + 6) + 1) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))))))), h, c⟩ =
      ⟨some .E, [], false :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (ones (2 * (n + 3)) ++ (false :: (false :: X)))))))))))))))))))))))))))))), h + (-4), c + (64 * n + 442)⟩ := by
  rw [show 2 * (n + 6) + 1 = 2 * n + 13 by ring, show 2 * (n + 3) = 2 * n + 6 by ring]
  have s0 : ∀ (h : ℤ) (c : ℕ), Zip.run 3 ⟨some .E, [], false :: (ones (2 * n + 13) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))))))), h, c⟩ =
      ⟨some .B, true :: (true :: []), ones (2 * n + 13) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))))))), h + (1), c + 3⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s1 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 13) (true :: (true :: [])) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))))))) h c
  have s2 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 15) ++ [], false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 15) ++ [], true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s3 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 15) ([]) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))))) h c
  have s4 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, [], ones (2 * n + 16) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: [])), ones (2 * n + 14) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s5 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 14) (false :: (false :: (true :: []))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))))) h c
  have s6 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 14) ++ (false :: (false :: (true :: []))), false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 14) ++ (false :: (false :: (true :: []))), true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s7 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 14) (false :: (false :: (true :: []))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))))) h c
  have s8 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: [])), ones (2 * n + 15) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: [])))), ones (2 * n + 13) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s9 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 13) (false :: (false :: (true :: (false :: (true :: []))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))))) h c
  have s10 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 13) ++ (false :: (false :: (true :: (false :: (true :: []))))), false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 13) ++ (false :: (false :: (true :: (false :: (true :: []))))), true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s11 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 13) (false :: (false :: (true :: (false :: (true :: []))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))) h c
  have s12 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: (false :: (true :: [])))), ones (2 * n + 14) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))), ones (2 * n + 12) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s13 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 12) (false :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))))) h c
  have s14 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 12) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))), false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 12) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))), true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s15 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 12) (false :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))) h c
  have s16 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))), ones (2 * n + 13) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))), ones (2 * n + 11) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s17 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 11) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))))) h c
  have s18 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 11) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))), false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 11) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))), true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s19 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 11) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))) h c
  have s20 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))), ones (2 * n + 12) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))), ones (2 * n + 10) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s21 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 10) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))))) h c
  have s22 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 10) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))), false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 10) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))), true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s23 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 10) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))) h c
  have s24 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))), ones (2 * n + 11) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))), ones (2 * n + 9) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s25 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 9) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))))) h c
  have s26 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 9) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))), false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 9) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))), true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s27 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 9) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))) h c
  have s28 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))), ones (2 * n + 10) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))), ones (2 * n + 8) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s29 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 8) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))))) h c
  have s30 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 8) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))), false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 8) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))), true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s31 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 8) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))) h c
  have s32 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))), ones (2 * n + 9) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))), ones (2 * n + 7) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s33 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 7) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))))) h c
  have s34 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 7) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))), false :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 7) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))), true :: (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s35 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 7) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))) h c
  have s36 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))), ones (2 * n + 8) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))), ones (2 * n + 6) ++ (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s37 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 6) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))) (false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))))) h c
  have s38 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 6) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))), false :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 6) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))), true :: (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s39 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 6) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))) (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))) h c
  have s40 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))), ones (2 * n + 7) ++ (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))), ones (2 * n + 5) ++ (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s41 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 5) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))) (false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))))) h c
  have s42 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 5) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))), false :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 5) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))), true :: (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s43 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 5) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))) (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))) h c
  have s44 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))), ones (2 * n + 6) ++ (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))))), ones (2 * n + 4) ++ (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s45 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 4) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))) (false :: (false :: (false :: (false :: (false :: (true :: (true :: X))))))) h c
  have s46 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 4) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))), false :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 4) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))), true :: (false :: (false :: (false :: (false :: (true :: (true :: X)))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s47 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 4) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))) (false :: (false :: (false :: (false :: (true :: (true :: X)))))) h c
  have s48 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))))), ones (2 * n + 5) ++ (false :: (false :: (false :: (false :: (true :: (true :: X)))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))))))), ones (2 * n + 3) ++ (false :: (false :: (false :: (false :: (true :: (true :: X)))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s49 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 3) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))) (false :: (false :: (false :: (false :: (true :: (true :: X)))))) h c
  have s50 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 3) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))), false :: (false :: (false :: (false :: (true :: (true :: X))))), h, c⟩ =
      ⟨some .F, ones (2 * n + 3) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))), true :: (false :: (false :: (false :: (true :: (true :: X))))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s51 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 3) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))) (false :: (false :: (false :: (true :: (true :: X))))) h c
  have s52 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))))))), ones (2 * n + 4) ++ (false :: (false :: (false :: (true :: (true :: X))))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))))))))), ones (2 * n + 2) ++ (false :: (false :: (false :: (true :: (true :: X))))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s53 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 2) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))))) (false :: (false :: (false :: (true :: (true :: X))))) h c
  have s54 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 2) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))))), false :: (false :: (false :: (true :: (true :: X)))), h, c⟩ =
      ⟨some .F, ones (2 * n + 2) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))))), true :: (false :: (false :: (true :: (true :: X)))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s55 := fun (h : ℤ) (c : ℕ) => crossF (2 * n + 2) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))))) (false :: (false :: (true :: (true :: X)))) h c
  have s56 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .F, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))))))))), ones (2 * n + 3) ++ (false :: (false :: (true :: (true :: X)))), h, c⟩ =
      ⟨some .B, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))))))))))), ones (2 * n + 1) ++ (false :: (false :: (true :: (true :: X)))), h + (2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s57 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 1) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))))))) (false :: (false :: (true :: (true :: X)))) h c
  have s58 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 1) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))))))), false :: (false :: (true :: (true :: X))), h, c⟩ =
      ⟨some .E, ones (2 * n + 1) ++ (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))))))), true :: (false :: (false :: (true :: X))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s59 := fun (h : ℤ) (c : ℕ) => crossE (2 * n + 1) (false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))))))) (false :: (false :: (true :: X))) h c
  have s60 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .E, false :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))))))))))), ones (2 * n + 2) ++ (false :: (false :: (true :: X))), h, c⟩ =
      ⟨some .B, true :: (true :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))))))))))), ones (2 * n + 2) ++ (false :: (false :: (true :: X))), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s61 := fun (h : ℤ) (c : ℕ) => crossB (2 * n + 2) (true :: (true :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))))))) (false :: (false :: (true :: X))) h c
  have s62 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, ones (2 * n + 5) ++ (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))))))))), false :: (false :: (true :: X)), h, c⟩ =
      ⟨some .E, ones (2 * n + 5) ++ (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))))))))), true :: (false :: (false :: X)), h + (0), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s63 := fun (h : ℤ) (c : ℕ) => crossE (2 * n + 5) (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: [])))))))))))))))))))))))))) (false :: (false :: X)) h c
  have s64 : ∀ (h : ℤ) (c : ℕ), Zip.run 36 ⟨some .E, false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))))))))))))))))), ones (2 * n + 6) ++ (false :: (false :: X)), h, c⟩ =
      ⟨some .C, true :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))), false :: (true :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (ones (2 * n + 6) ++ (false :: (false :: X)))))))))))))))), h + (-14), c + 36⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s65 : ∀ (h : ℤ) (c : ℕ), Zip.run 34 ⟨some .C, true :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: (false :: (true :: []))))))))))), false :: (true :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (ones (2 * n + 6) ++ (false :: (false :: X)))))))))))))))), h, c⟩ =
      ⟨some .E, [], false :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (true :: (true :: (false :: (false :: (ones (2 * n + 6) ++ (false :: (false :: X)))))))))))))))))))))))))))))), h + (-14), c + 34⟩ := by
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
  have e17 := chainB e16 (s17 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e18 := chainB e17 (s18 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e19 := chainB e18 (s19 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e20 := chainB e19 (s20 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e21 := chainB e20 (s21 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e22 := chainB e21 (s22 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e23 := chainB e22 (s23 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e24 := chainB e23 (s24 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e25 := chainB e24 (s25 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e26 := chainB e25 (s26 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e27 := chainB e26 (s27 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e28 := chainB e27 (s28 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e29 := chainB e28 (s29 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e30 := chainB e29 (s30 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e31 := chainB e30 (s31 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e32 := chainB e31 (s32 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e33 := chainB e32 (s33 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e34 := chainB e33 (s34 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e35 := chainB e34 (s35 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e36 := chainB e35 (s36 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e37 := chainB e36 (s37 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e38 := chainB e37 (s38 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e39 := chainB e38 (s39 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e40 := chainB e39 (s40 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e41 := chainB e40 (s41 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e42 := chainB e41 (s42 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e43 := chainB e42 (s43 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e44 := chainB e43 (s44 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e45 := chainB e44 (s45 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e46 := chainB e45 (s46 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e47 := chainB e46 (s47 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e48 := chainB e47 (s48 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e49 := chainB e48 (s49 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e50 := chainB e49 (s50 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e51 := chainB e50 (s51 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e52 := chainB e51 (s52 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e53 := chainB e52 (s53 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e54 := chainB e53 (s54 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e55 := chainB e54 (s55 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e56 := chainB e55 (s56 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e57 := chainB e56 (s57 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e58 := chainB e57 (s58 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e59 := chainB e58 (s59 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e60 := chainB e59 (s60 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e61 := chainB e60 (s61 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e62 := chainB e61 (s62 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e63 := chainB e62 (s63 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e64 := chainB e63 (s64 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  have e65 := chainB e64 (s65 _ _) (zip_eq rfl (by simp) (by simp) rfl rfl)
  refine (congrArg (fun t => Zip.run t _) (show (64 * n + 442) = 3 + (2 * n + 13) + 4 + (2 * n + 15) + 4 + (2 * n + 14) + 4 + (2 * n + 14) + 4 + (2 * n + 13) + 4 + (2 * n + 13) + 4 + (2 * n + 12) + 4 + (2 * n + 12) + 4 + (2 * n + 11) + 4 + (2 * n + 11) + 4 + (2 * n + 10) + 4 + (2 * n + 10) + 4 + (2 * n + 9) + 4 + (2 * n + 9) + 4 + (2 * n + 8) + 4 + (2 * n + 8) + 4 + (2 * n + 7) + 4 + (2 * n + 7) + 4 + (2 * n + 6) + 4 + (2 * n + 6) + 4 + (2 * n + 5) + 4 + (2 * n + 5) + 4 + (2 * n + 4) + 4 + (2 * n + 4) + 4 + (2 * n + 3) + 4 + (2 * n + 3) + 4 + (2 * n + 2) + 4 + (2 * n + 2) + 4 + (2 * n + 1) + 4 + (2 * n + 1) + 4 + (2 * n + 2) + 4 + (2 * n + 5) + 36 + 34 by ring)).trans (e65.trans ?_)
  exact zip_eq rfl (by simp) (by simp) (by push_cast; ring) (by ring)

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.rule_R23_6
