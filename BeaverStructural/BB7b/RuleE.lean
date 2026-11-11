import BeaverStructural.BB7b.Loops
import BeaverStructural.BB7b.RuleR4pre
import BeaverStructural.BB7b.Numbers

/-! Rule E of the BB(7) machine of October 2026: from K(a; 0^20) with a = m + 7 the machine halts. The mini-cycles,
the sweep and the turn at the boundary, 6m + 7 forward passes into the blank tape, the last pass, 3m + 3 backward
passes, and the halting row. The halted tape is stated cell for cell, with its number of ones. -/

namespace BeaverStructural.BB7b

/-- The halted configuration: left of the head `1 1 0 0 1 1 (0 1)^39`, right of it `1 0 0 (1100)^(3m+2) 1 0 0 0`. -/
abbrev halted (m : ℕ) (h : ℤ) (c : ℕ) : Zip :=
  ⟨none, true :: true :: false :: false :: true :: true :: tr 39,
    true :: false :: false :: (c4 (3 * m + 2) ++ true :: false :: false :: false :: []), h, c⟩


/-- Rule E, twenty zero digits. -/
theorem rule_E (m : ℕ) (h : ℤ) (c : ℕ) :
    ∃ hd : ℤ, Zip.run (costE m)
        (kc [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 7) 0 h c) =
      halted m hd (c + costE m) := by
  have m1 : Zip.run (12 * (m + 7) * (m + 7) + 18 * (m + 7))
      (kc [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 7) 0 h c) =
      kc [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0 (3 * m + 21) (h - 4 * ((m : ℤ) + 7))
        (c + (12 * (m + 7) * (m + 7) + 18 * (m + 7))) := by
    have q := miniCycles (2 * (m + 7)) 1
      (false :: false :: rgt [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) h c
    rw [show 2 * 1 * (2 * (m + 7)) + 3 * (2 * (m + 7)) * (2 * (m + 7)) + 7 * (2 * (m + 7)) =
        12 * (m + 7) * (m + 7) + 18 * (m + 7) by ring,
      show 1 + 3 * (2 * (m + 7)) = 2 * (3 * m + 21) + 1 by ring] at q
    exact q.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  have m2 : Zip.run (176 * (3 * m) + 2425)
      (kc [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 0 (3 * m + 21) (h - 4 * ((m : ℤ) + 7))
        (c + (12 * (m + 7) * (m + 7) + 18 * (m + 7)))) =
      ⟨some .F, true :: tr 40, false :: (ones (2 * (3 * m) + 8) ++ false :: false :: []),
        h - 4 * ((m : ℤ) + 7) + 79, c + (12 * (m + 7) * (m + 7) + 18 * (m + 7)) + (176 * (3 * m) + 2425)⟩ :=
    rule_R4pre (3 * m) _ _
  have m3 : Zip.run ((6 * m + 7) * (6 * m + 7) + (2 * 0 + 7) * (6 * m + 7))
      ⟨some .F, true :: tr 40, false :: (ones (2 * (3 * m) + 8) ++ false :: false :: []),
        h - 4 * ((m : ℤ) + 7) + 79, c + (12 * (m + 7) * (m + 7) + 18 * (m + 7)) + (176 * (3 * m) + 2425)⟩ =
      ⟨some .F, tr (6 * m + 7) ++ true :: tr 40, false :: (ones (0 + 1) ++ false :: false :: []),
        h - 4 * ((m : ℤ) + 7) + 79 + 2 * ((6 * m + 7 : ℕ) : ℤ),
        c + (12 * (m + 7) * (m + 7) + 18 * (m + 7)) + (176 * (3 * m) + 2425) +
          ((6 * m + 7) * (6 * m + 7) + (2 * 0 + 7) * (6 * m + 7))⟩ := by
    have q := forwardPasses (6 * m + 7) 0 (true :: tr 40) (h - 4 * ((m : ℤ) + 7) + 79)
      (c + (12 * (m + 7) * (m + 7) + 18 * (m + 7)) + (176 * (3 * m) + 2425))
    rw [show 6 * m + 7 + 0 + 1 = 2 * (3 * m) + 8 by ring] at q
    exact q
  have m4 : Zip.run 9
      ⟨some .F, tr (6 * m + 7) ++ true :: tr 40, false :: (ones (0 + 1) ++ false :: false :: []),
        h - 4 * ((m : ℤ) + 7) + 79 + 2 * ((6 * m + 7 : ℕ) : ℤ),
        c + (12 * (m + 7) * (m + 7) + 18 * (m + 7)) + (176 * (3 * m) + 2425) +
          ((6 * m + 7) * (6 * m + 7) + (2 * 0 + 7) * (6 * m + 7))⟩ =
      ⟨some .F, true :: (tr (6 * m + 5) ++ true :: tr 40),
        false :: true :: false :: true :: false :: false :: false :: [],
        h - 4 * ((m : ℤ) + 7) + 79 + 2 * ((6 * m + 7 : ℕ) : ℤ) + (-3),
        c + (12 * (m + 7) * (m + 7) + 18 * (m + 7)) + (176 * (3 * m) + 2425) +
          ((6 * m + 7) * (6 * m + 7) + (2 * 0 + 7) * (6 * m + 7)) + 9⟩ :=
    rule_END2 false (true :: (tr (6 * m + 5) ++ true :: tr 40)) _ _
  have hW : true :: (tr (6 * m + 5) ++ true :: tr 40) = (q4 (3 * m + 3) ++ true :: tr 40).tail := by
    have e : tr (6 * m + 5) ++ true :: tr 40 = false :: true :: (q4 (3 * m + 2) ++ true :: tr 40) := by
      rw [show 6 * m + 5 = 2 * (3 * m + 2) + 1 by ring]
      show false :: true :: (tr (2 * (3 * m + 2)) ++ true :: tr 40) = _
      rw [tr_double]
    rw [e]
    rfl
  have m5 : Zip.run (10 * (3 * m + 3))
      ⟨some .F, true :: (tr (6 * m + 5) ++ true :: tr 40),
        false :: true :: false :: true :: false :: false :: false :: [],
        h - 4 * ((m : ℤ) + 7) + 79 + 2 * ((6 * m + 7 : ℕ) : ℤ) + (-3),
        c + (12 * (m + 7) * (m + 7) + 18 * (m + 7)) + (176 * (3 * m) + 2425) +
          ((6 * m + 7) * (6 * m + 7) + (2 * 0 + 7) * (6 * m + 7)) + 9⟩ =
      ⟨some .F, tr 40, true :: true :: false :: (c4 (3 * m + 3) ++ true :: false :: false :: false :: []),
        h - 4 * ((m : ℤ) + 7) + 79 + 2 * ((6 * m + 7 : ℕ) : ℤ) + (-3) - 4 * ((3 * m + 3 : ℕ) : ℤ),
        c + (12 * (m + 7) * (m + 7) + 18 * (m + 7)) + (176 * (3 * m) + 2425) +
          ((6 * m + 7) * (6 * m + 7) + (2 * 0 + 7) * (6 * m + 7)) + 9 + 10 * (3 * m + 3)⟩ := by
    rw [hW]
    exact backwardPasses (3 * m + 3) true (tr 40) (true :: false :: false :: false :: []) _ _
  have m6 : Zip.run 6
      ⟨some .F, tr 40, true :: true :: false :: (c4 (3 * m + 3) ++ true :: false :: false :: false :: []),
        h - 4 * ((m : ℤ) + 7) + 79 + 2 * ((6 * m + 7 : ℕ) : ℤ) + (-3) - 4 * ((3 * m + 3 : ℕ) : ℤ),
        c + (12 * (m + 7) * (m + 7) + 18 * (m + 7)) + (176 * (3 * m) + 2425) +
          ((6 * m + 7) * (6 * m + 7) + (2 * 0 + 7) * (6 * m + 7)) + 9 + 10 * (3 * m + 3)⟩ =
      halted m (h - 4 * ((m : ℤ) + 7) + 79 + 2 * ((6 * m + 7 : ℕ) : ℤ) + (-3) - 4 * ((3 * m + 3 : ℕ) : ℤ) + 4)
        (c + (12 * (m + 7) * (m + 7) + 18 * (m + 7)) + (176 * (3 * m) + 2425) +
          ((6 * m + 7) * (6 * m + 7) + (2 * 0 + 7) * (6 * m + 7)) + 9 + 10 * (3 * m + 3) + 6) :=
    rule_R4fin (true :: tr 39) (true :: false :: false :: (c4 (3 * m + 2) ++ true :: false :: false :: false :: [])) _ _
  refine ⟨h - 4 * ((m : ℤ) + 7) + 79 + 2 * ((6 * m + 7 : ℕ) : ℤ) + (-3) - 4 * ((3 * m + 3 : ℕ) : ℤ) + 4, ?_⟩
  have all := chain (chain (chain (chain (chain m1 m2) m3) m4) m5) m6
  refine (congrArg (fun k => Zip.run k _) (show costE m = 12 * (m + 7) * (m + 7) + 18 * (m + 7) +
      (176 * (3 * m) + 2425) + ((6 * m + 7) * (6 * m + 7) + (2 * 0 + 7) * (6 * m + 7)) + 9 + 10 * (3 * m + 3) + 6 by
        unfold costE; ring)).trans (all.trans ?_)
  exact zip_eq rfl rfl rfl rfl (by unfold costE; ring)

/-- The halted tape holds 6a + 7 ones, a = m + 7. -/
theorem halted_ones (m : ℕ) (h : ℤ) (c : ℕ) :
    (halted m h c).left.count true + (halted m h c).right.count true = 6 * (m + 7) + 7 := by
  have t : ∀ j, (tr j).count true = j := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => simp [ih]
  have q : ∀ i (T : List Bool), (c4 i ++ T).count true = 2 * i + T.count true := by
    intro i T
    induction i with
    | zero => simp
    | succ i ih => simp [ih]; ring
  simp only [halted, List.count_cons, t, q]
  simp
  ring

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.rule_E
#print axioms BeaverStructural.BB7b.halted_ones
