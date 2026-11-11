import BeaverStructural.BB7b.Loops
import BeaverStructural.BB7b.StepR23

/-! The macro rules D and B1 .. B19 on the configurations `kc`: the mini-cycles, then the sweep rule. -/

namespace BeaverStructural.BB7b

/-- Rule D: one unit of the active digit is cleared and the accumulator a becomes 3a + 3. -/
theorem rule_D (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 0) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (16 * n + 58)) (kc ((y + 1) :: t) a 0 h c) =
      kc (y :: t) (n + 3) 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (16 * n + 58))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc ((y + 1) :: t) a 0 h c) =
      kc ((y + 1) :: t) 0 (n + 0) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt ((y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 0) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_0 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B1: 1 zero digits in front of the digit y + 1, with 3a = n + 1. -/
theorem rule_B_1 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 1) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (24 * n + 102)) (kc (0 :: (y + 1) :: t) a 0 h c) =
      kc ((n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (24 * n + 102))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: (y + 1) :: t) 0 (n + 1) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 1) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_1 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B2: 2 zero digits in front of the digit y + 1, with 3a = n + 2. -/
theorem rule_B_2 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 2) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (32 * n + 154)) (kc (0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (32 * n + 154))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: (y + 1) :: t) 0 (n + 2) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 2) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_2 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B3: 3 zero digits in front of the digit y + 1, with 3a = n + 3. -/
theorem rule_B_3 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 3) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (40 * n + 214)) (kc (0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (40 * n + 214))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 3) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 3) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_3 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B4: 4 zero digits in front of the digit y + 1, with 3a = n + 4. -/
theorem rule_B_4 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 4) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (48 * n + 282)) (kc (0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (48 * n + 282))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 4) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 4) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_4 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B5: 5 zero digits in front of the digit y + 1, with 3a = n + 5. -/
theorem rule_B_5 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 5) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (56 * n + 358)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (56 * n + 358))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 5) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 5) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_5 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B6: 6 zero digits in front of the digit y + 1, with 3a = n + 6. -/
theorem rule_B_6 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 6) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (64 * n + 442)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (64 * n + 442))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 6) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 6) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_6 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B7: 7 zero digits in front of the digit y + 1, with 3a = n + 7. -/
theorem rule_B_7 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 7) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (72 * n + 534)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (72 * n + 534))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 7) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 7) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_7 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B8: 8 zero digits in front of the digit y + 1, with 3a = n + 8. -/
theorem rule_B_8 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 8) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (80 * n + 634)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (80 * n + 634))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 8) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 8) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_8 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B9: 9 zero digits in front of the digit y + 1, with 3a = n + 9. -/
theorem rule_B_9 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 9) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (88 * n + 742)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (88 * n + 742))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 9) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 9) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_9 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B10: 10 zero digits in front of the digit y + 1, with 3a = n + 10. -/
theorem rule_B_10 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 10) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (96 * n + 858)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (96 * n + 858))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 10) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 10) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_10 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B11: 11 zero digits in front of the digit y + 1, with 3a = n + 11. -/
theorem rule_B_11 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 11) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (104 * n + 982)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (104 * n + 982))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 11) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 11) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_11 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B12: 12 zero digits in front of the digit y + 1, with 3a = n + 12. -/
theorem rule_B_12 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 12) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (112 * n + 1114)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (112 * n + 1114))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 12) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 12) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_12 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B13: 13 zero digits in front of the digit y + 1, with 3a = n + 13. -/
theorem rule_B_13 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 13) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (120 * n + 1254)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (120 * n + 1254))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 13) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 13) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_13 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B14: 14 zero digits in front of the digit y + 1, with 3a = n + 14. -/
theorem rule_B_14 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 14) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (128 * n + 1402)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (128 * n + 1402))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 14) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 14) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_14 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B15: 15 zero digits in front of the digit y + 1, with 3a = n + 15. -/
theorem rule_B_15 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 15) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (136 * n + 1558)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (136 * n + 1558))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 15) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 15) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_15 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B16: 16 zero digits in front of the digit y + 1, with 3a = n + 16. -/
theorem rule_B_16 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 16) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (144 * n + 1722)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (144 * n + 1722))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 16) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 16) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_16 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B17: 17 zero digits in front of the digit y + 1, with 3a = n + 17. -/
theorem rule_B_17 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 17) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (152 * n + 1894)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (152 * n + 1894))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 17) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 17) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_17 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B18: 18 zero digits in front of the digit y + 1, with 3a = n + 18. -/
theorem rule_B_18 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 18) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (160 * n + 2074)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (160 * n + 2074))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 18) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 18) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_18 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

/-- Rule B19: 19 zero digits in front of the digit y + 1, with 3a = n + 19. -/
theorem rule_B_19 (a n y : ℕ) (t : List ℕ) (hn : 3 * a = n + 19) (h : ℤ) (c : ℕ) :
    Zip.run (12 * a * a + 18 * a + (168 * n + 2262)) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + (12 * a * a + 18 * a + (168 * n + 2262))) := by
  have m : Zip.run (12 * a * a + 18 * a) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) a 0 h c) =
      kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 19) (h - 4 * (a : ℤ)) (c + (12 * a * a + 18 * a)) := by
    have m := miniCycles (2 * a) 1 (false :: false :: rgt (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t)) h c
    rw [show 2 * 1 * (2 * a) + 3 * (2 * a) * (2 * a) + 7 * (2 * a) = 12 * a * a + 18 * a by ring,
      show 1 + 3 * (2 * a) = 2 * (n + 19) + 1 by omega] at m
    exact m.trans (zip_eq rfl rfl rfl (by push_cast; ring) rfl)
  exact (chain m (step_R23_19 n y t _ _)).trans (zip_eq rfl rfl rfl rfl (by ring))

end BeaverStructural.BB7b

