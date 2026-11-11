import BeaverStructural.BB7.Machine
/-! R3_1 from the rows of the BB(7) champion. -/

namespace BeaverStructural.BB7

/-- R3_1: the published low-level rule, run from the rows in exactly its cost; the left context L is never read. -/
theorem rule_R3_1 (n : ℕ) (L : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (32 * n + 274) ⟨some .A, false :: (false :: (true :: (true :: (true :: (false :: (false :: (pw true false (n) ++ (true :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (pw true false (3) ++ L)))))))))))))))), [], h, c⟩ =
      ⟨some .A, false :: (false :: (true :: (true :: (true :: (false :: (false :: (true :: (false :: (true :: (true :: (true :: (false :: (true :: (pw true false (n + 6) ++ (true :: L))))))))))))))), [], h + (6), c + (32 * n + 274)⟩ := by
  have s0 : ∀ (h : ℤ) (c : ℕ), Zip.run 21 ⟨some .A, false :: (false :: (true :: (true :: (true :: (false :: (false :: (pw true false (n) ++ (true :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (pw true false (3) ++ L)))))))))))))))), [], h, c⟩ =
      ⟨some .B, pw true false (n) ++ (true :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (pw true false (3) ++ L))))))))), false :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))), h + (-7), c + 21⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s1 := fun (h : ℤ) (c : ℕ) => sweepB (n) (true :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (pw true false (3) ++ L))))))))) (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))) h c
  have s2 : ∀ (h : ℤ) (c : ℕ), Zip.run 5 ⟨some .B, true :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (pw true false (3) ++ L)))))))), false :: (pw false true (n) ++ (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))), h, c⟩ =
      ⟨some .A, true :: (true :: (true :: (false :: (true :: (pw true false (3) ++ L))))), true :: (pw true false (n + 1) ++ (true :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))), h + (-3), c + 5⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s3 := fun (h : ℤ) (c : ℕ) => sweepA (n + 1) (true :: (true :: (true :: (false :: (true :: (pw true false (3) ++ L)))))) (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))) h c
  have s4 : ∀ (h : ℤ) (c : ℕ), Zip.run 10 ⟨some .A, pw true false (n + 1) ++ (true :: (true :: (true :: (false :: (true :: (pw true false (3) ++ L)))))), true :: (true :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))), h, c⟩ =
      ⟨some .B, pw true false (n) ++ (true :: (true :: (true :: (false :: (true :: (pw true false (3) ++ L)))))), false :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))))), h + (-2), c + 10⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s5 := fun (h : ℤ) (c : ℕ) => sweepB (n) (true :: (true :: (true :: (false :: (true :: (pw true false (3) ++ L)))))) (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))))) h c
  have s6 : ∀ (h : ℤ) (c : ℕ), Zip.run 5 ⟨some .B, true :: (true :: (true :: (false :: (true :: (pw true false (3) ++ L))))), false :: (pw false true (n) ++ (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))))), h, c⟩ =
      ⟨some .A, true :: (true :: (pw true false (3) ++ L)), true :: (pw true false (n + 1) ++ (true :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))))))), h + (-3), c + 5⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s7 := fun (h : ℤ) (c : ℕ) => sweepA (n + 1) (true :: (true :: (pw true false (3) ++ L))) (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))))) h c
  have s8 : ∀ (h : ℤ) (c : ℕ), Zip.run 10 ⟨some .A, pw true false (n + 1) ++ (true :: (true :: (pw true false (3) ++ L))), true :: (true :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))))), h, c⟩ =
      ⟨some .B, pw true false (n) ++ (true :: (true :: (pw true false (3) ++ L))), false :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))))))), h + (-2), c + 10⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s9 := fun (h : ℤ) (c : ℕ) => sweepB (n) (true :: (true :: (pw true false (3) ++ L))) (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))))))) h c
  have s10 : ∀ (h : ℤ) (c : ℕ), Zip.run 5 ⟨some .B, true :: (true :: (pw true false (3) ++ L)), false :: (pw false true (n) ++ (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))))))))), h, c⟩ =
      ⟨some .A, true :: (pw true false (2) ++ L), true :: (pw true false (n + 1) ++ (true :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))))))))), h + (-3), c + 5⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s11 := fun (h : ℤ) (c : ℕ) => sweepA (n + 1) (true :: (pw true false (2) ++ L)) (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))))))) h c
  have s12 : ∀ (h : ℤ) (c : ℕ), Zip.run 10 ⟨some .A, pw true false (n + 1) ++ (true :: (pw true false (2) ++ L)), true :: (true :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))))))))), h, c⟩ =
      ⟨some .B, pw true false (n) ++ (true :: (pw true false (2) ++ L)), false :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))))))))))), h + (-2), c + 10⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s13 := fun (h : ℤ) (c : ℕ) => sweepB (n) (true :: (pw true false (2) ++ L)) (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))))))))))) h c
  have s14 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, true :: (pw true false (2) ++ L), false :: (pw false true (n) ++ (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))))))))))), h, c⟩ =
      ⟨some .G, true :: (pw true false (1) ++ L), pw true false (n + 2) ++ (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))))))))), h + (-2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s15 := fun (h : ℤ) (c : ℕ) => sweepG (n + 2) (true :: (pw true false (1) ++ L)) (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))))))))) h c
  have s16 : ∀ (h : ℤ) (c : ℕ), Zip.run 40 ⟨some .G, pw true false (n + 2) ++ (true :: (pw true false (1) ++ L)), false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))))))))), h, c⟩ =
      ⟨some .E, true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (true :: (true :: (false :: (false :: (pw true false (n + 2) ++ (true :: (pw true false (1) ++ L)))))))))))))))), true :: (true :: (false :: (true :: []))), h + (14), c + 40⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s17 : ∀ (h : ℤ) (c : ℕ), Zip.run 30 ⟨some .E, true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (true :: (true :: (false :: (false :: (pw true false (n + 2) ++ (true :: (pw true false (1) ++ L)))))))))))))))), true :: (true :: (false :: (true :: []))), h, c⟩ =
      ⟨some .B, pw true false (n + 2) ++ (true :: (pw true false (1) ++ L)), false :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (true :: []))))))))))))))))), h + (-14), c + 30⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s18 := fun (h : ℤ) (c : ℕ) => sweepB (n + 2) (true :: (pw true false (1) ++ L)) (false :: (false :: (true :: (false :: (true :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (true :: []))))))))))))))))) h c
  have s19 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, true :: (pw true false (1) ++ L), false :: (pw false true (n + 2) ++ (false :: (false :: (true :: (false :: (true :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (true :: [])))))))))))))))))), h, c⟩ =
      ⟨some .G, true :: L, pw true false (n + 4) ++ (false :: (true :: (false :: (true :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (true :: [])))))))))))))))), h + (-2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s20 := fun (h : ℤ) (c : ℕ) => sweepG (n + 4) (true :: L) (false :: (true :: (false :: (true :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (true :: [])))))))))))))))) h c
  have s21 : ∀ (h : ℤ) (c : ℕ), Zip.run 40 ⟨some .G, pw true false (n + 4) ++ (true :: L), false :: (true :: (false :: (true :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (false :: (true :: (false :: (true :: []))))))))))))))), h, c⟩ =
      ⟨some .B, true :: (true :: (false :: (true :: (false :: (true :: (pw true false (n + 6) ++ (true :: L))))))), false :: (false :: (true :: (true :: (false :: (true :: []))))), h + (10), c + 40⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s22 : ∀ (h : ℤ) (c : ℕ), Zip.run 40 ⟨some .B, true :: (true :: (false :: (true :: (false :: (true :: (pw true false (n + 6) ++ (true :: L))))))), false :: (false :: (true :: (true :: (false :: (true :: []))))), h, c⟩ =
      ⟨some .F, true :: (true :: (false :: (true :: (pw true false (n + 6) ++ (true :: L))))), false :: (true :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))), h + (-2), c + 40⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s23 : ∀ (h : ℤ) (c : ℕ), Zip.run 16 ⟨some .F, true :: (true :: (false :: (true :: (pw true false (n + 6) ++ (true :: L))))), false :: (true :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))), h, c⟩ =
      ⟨some .A, false :: (false :: (true :: (true :: (true :: (false :: (false :: (true :: (false :: (true :: (true :: (true :: (false :: (true :: (pw true false (n + 6) ++ (true :: L))))))))))))))), [], h + (10), c + 16⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have e0 := s0 h c
  have e1 := chain e0 (s1 _ _)
  have e2 := chain e1 (s2 _ _)
  have e3 := chain e2 (s3 _ _)
  have e4 := chain e3 (s4 _ _)
  have e5 := chain e4 (s5 _ _)
  have e6 := chain e5 (s6 _ _)
  have e7 := chain e6 (s7 _ _)
  have e8 := chain e7 (s8 _ _)
  have e9 := chain e8 (s9 _ _)
  have e10 := chain e9 (s10 _ _)
  have e11 := chain e10 (s11 _ _)
  have e12 := chain e11 (s12 _ _)
  have e13 := chain e12 (s13 _ _)
  have e14 := chain e13 (s14 _ _)
  have e15 := chain e14 (s15 _ _)
  have e16 := chain e15 (s16 _ _)
  have e17 := chain e16 (s17 _ _)
  have e18 := chain e17 (s18 _ _)
  have e19 := chain e18 (s19 _ _)
  have e20 := chain e19 (s20 _ _)
  have e21 := chain e20 (s21 _ _)
  have e22 := chain e21 (s22 _ _)
  have e23 := chain e22 (s23 _ _)
  refine (congrArg (fun t => Zip.run t _) (show (32 * n + 274) = 21 + 2 * (n) + 5 + 6 * (n + 1) + 10 + 2 * (n) + 5 + 6 * (n + 1) + 10 + 2 * (n) + 5 + 6 * (n + 1) + 10 + 2 * (n) + 4 + 2 * (n + 2) + 40 + 30 + 2 * (n + 2) + 4 + 2 * (n + 4) + 40 + 40 + 16 by ring)).trans (e23.trans ?_)
  exact zip_eq rfl (by simp) (by simp) (by push_cast; ring) (by ring)

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.rule_R3_1
