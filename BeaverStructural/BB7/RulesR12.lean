import BeaverStructural.BB7.Machine
/-! R1, R2 from the rows of the BB(7) champion. -/

namespace BeaverStructural.BB7

/-- R1: the published low-level rule, run from the rows in exactly its cost; the left context L is never read. -/
theorem rule_R1 (n : ℕ) (L : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (4 * n + 42) ⟨some .A, false :: (false :: (true :: (true :: (true :: (false :: (false :: (pw true false (n) ++ (true :: (true :: (false :: L)))))))))), [], h, c⟩ =
      ⟨some .A, false :: (false :: (true :: (true :: (true :: (false :: (false :: (pw true false (n + 2) ++ (true :: L)))))))), [], h + (2), c + (4 * n + 42)⟩ := by
  have s0 : ∀ (h : ℤ) (c : ℕ), Zip.run 21 ⟨some .A, false :: (false :: (true :: (true :: (true :: (false :: (false :: (pw true false (n) ++ (true :: (true :: (false :: L)))))))))), [], h, c⟩ =
      ⟨some .B, pw true false (n) ++ (true :: (true :: (false :: L))), false :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))), h + (-7), c + 21⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s1 := fun (h : ℤ) (c : ℕ) => sweepB (n) (true :: (true :: (false :: L))) (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))) h c
  have s2 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, true :: (true :: (false :: L)), false :: (pw false true (n) ++ (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))), h, c⟩ =
      ⟨some .G, true :: L, pw true false (n + 2) ++ (false :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))), h + (-2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s3 := fun (h : ℤ) (c : ℕ) => sweepG (n + 2) (true :: L) (false :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))) h c
  have s4 : ∀ (h : ℤ) (c : ℕ), Zip.run 13 ⟨some .G, pw true false (n + 2) ++ (true :: L), false :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))), h, c⟩ =
      ⟨some .A, false :: (false :: (true :: (true :: (true :: (false :: (false :: (pw true false (n + 2) ++ (true :: L)))))))), [], h + (7), c + 13⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have e0 := s0 h c
  have e1 := chain e0 (s1 _ _)
  have e2 := chain e1 (s2 _ _)
  have e3 := chain e2 (s3 _ _)
  have e4 := chain e3 (s4 _ _)
  refine (congrArg (fun t => Zip.run t _) (show (4 * n + 42) = 21 + 2 * (n) + 4 + 2 * (n + 2) + 13 by ring)).trans (e4.trans ?_)
  exact zip_eq rfl (by simp) (by simp) (by push_cast; ring) (by ring)

/-- R2: the published low-level rule, run from the rows in exactly its cost; the left context L is never read. -/
theorem rule_R2 (n : ℕ) (L : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (16 * n + 178) ⟨some .A, false :: (false :: (true :: (true :: (true :: (false :: (false :: (pw true false (n) ++ (true :: (true :: (pw true false (3) ++ L)))))))))), [], h, c⟩ =
      ⟨some .A, false :: (false :: (true :: (true :: (true :: (false :: (false :: (true :: (false :: (true :: (pw true false (n + 5) ++ (true :: L))))))))))), [], h + (6), c + (16 * n + 178)⟩ := by
  have s0 : ∀ (h : ℤ) (c : ℕ), Zip.run 21 ⟨some .A, false :: (false :: (true :: (true :: (true :: (false :: (false :: (pw true false (n) ++ (true :: (true :: (pw true false (3) ++ L)))))))))), [], h, c⟩ =
      ⟨some .B, pw true false (n) ++ (true :: (true :: (pw true false (3) ++ L))), false :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))), h + (-7), c + 21⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s1 := fun (h : ℤ) (c : ℕ) => sweepB (n) (true :: (true :: (pw true false (3) ++ L))) (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))) h c
  have s2 : ∀ (h : ℤ) (c : ℕ), Zip.run 5 ⟨some .B, true :: (true :: (pw true false (3) ++ L)), false :: (pw false true (n) ++ (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))), h, c⟩ =
      ⟨some .A, true :: (pw true false (2) ++ L), true :: (pw true false (n + 1) ++ (true :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))), h + (-3), c + 5⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s3 := fun (h : ℤ) (c : ℕ) => sweepA (n + 1) (true :: (pw true false (2) ++ L)) (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))) h c
  have s4 : ∀ (h : ℤ) (c : ℕ), Zip.run 10 ⟨some .A, pw true false (n + 1) ++ (true :: (pw true false (2) ++ L)), true :: (true :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))), h, c⟩ =
      ⟨some .B, pw true false (n) ++ (true :: (pw true false (2) ++ L)), false :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))))), h + (-2), c + 10⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s5 := fun (h : ℤ) (c : ℕ) => sweepB (n) (true :: (pw true false (2) ++ L)) (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))))) h c
  have s6 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, true :: (pw true false (2) ++ L), false :: (pw false true (n) ++ (false :: (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))))), h, c⟩ =
      ⟨some .G, true :: (pw true false (1) ++ L), pw true false (n + 2) ++ (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))), h + (-2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s7 := fun (h : ℤ) (c : ℕ) => sweepG (n + 2) (true :: (pw true false (1) ++ L)) (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))) h c
  have s8 : ∀ (h : ℤ) (c : ℕ), Zip.run 40 ⟨some .G, pw true false (n + 2) ++ (true :: (pw true false (1) ++ L)), false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: []))))))))), h, c⟩ =
      ⟨some .C, false :: (false :: (pw true false (n + 3) ++ (true :: (pw true false (1) ++ L)))), true :: (true :: (true :: (false :: (false :: (true :: (false :: (true :: []))))))), h + (4), c + 40⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s9 : ∀ (h : ℤ) (c : ℕ), Zip.run 6 ⟨some .C, false :: (false :: (pw true false (n + 3) ++ (true :: (pw true false (1) ++ L)))), true :: (true :: (true :: (false :: (false :: (true :: (false :: (true :: []))))))), h, c⟩ =
      ⟨some .B, pw true false (n + 2) ++ (true :: (pw true false (1) ++ L)), false :: (false :: (false :: (true :: (false :: (true :: (true :: (false :: (false :: (true :: (false :: (true :: []))))))))))), h + (-4), c + 6⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s10 := fun (h : ℤ) (c : ℕ) => sweepB (n + 2) (true :: (pw true false (1) ++ L)) (false :: (false :: (true :: (false :: (true :: (true :: (false :: (false :: (true :: (false :: (true :: []))))))))))) h c
  have s11 : ∀ (h : ℤ) (c : ℕ), Zip.run 4 ⟨some .B, true :: (pw true false (1) ++ L), false :: (pw false true (n + 2) ++ (false :: (false :: (true :: (false :: (true :: (true :: (false :: (false :: (true :: (false :: (true :: [])))))))))))), h, c⟩ =
      ⟨some .G, true :: L, pw true false (n + 4) ++ (false :: (true :: (false :: (true :: (true :: (false :: (false :: (true :: (false :: (true :: [])))))))))), h + (-2), c + 4⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s12 := fun (h : ℤ) (c : ℕ) => sweepG (n + 4) (true :: L) (false :: (true :: (false :: (true :: (true :: (false :: (false :: (true :: (false :: (true :: [])))))))))) h c
  have s13 : ∀ (h : ℤ) (c : ℕ), Zip.run 40 ⟨some .G, pw true false (n + 4) ++ (true :: L), false :: (true :: (false :: (true :: (true :: (false :: (false :: (true :: (false :: (true :: []))))))))), h, c⟩ =
      ⟨some .A, false :: (true :: (pw true false (n + 6) ++ (true :: L))), true :: (false :: (false :: (true :: (false :: (true :: []))))), h + (6), c + 40⟩ := by
    intro h c; simp [Zip.run, Zip.step, table] <;> omega
  have s14 : ∀ (h : ℤ) (c : ℕ), Zip.run 26 ⟨some .A, false :: (true :: (pw true false (n + 6) ++ (true :: L))), true :: (false :: (false :: (true :: (false :: (true :: []))))), h, c⟩ =
      ⟨some .A, false :: (false :: (true :: (true :: (true :: (false :: (false :: (true :: (false :: (true :: (pw true false (n + 5) ++ (true :: L))))))))))), [], h + (6), c + 26⟩ := by
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
  refine (congrArg (fun t => Zip.run t _) (show (16 * n + 178) = 21 + 2 * (n) + 5 + 6 * (n + 1) + 10 + 2 * (n) + 4 + 2 * (n + 2) + 40 + 6 + 2 * (n + 2) + 4 + 2 * (n + 4) + 40 + 26 by ring)).trans (e14.trans ?_)
  exact zip_eq rfl (by simp) (by simp) (by push_cast; ring) (by ring)

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.rule_R1
#print axioms BeaverStructural.BB7.rule_R2
