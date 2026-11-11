import BeaverStructural.BB7b.RuleR23_0
import BeaverStructural.BB7b.RuleR23_1
import BeaverStructural.BB7b.RuleR23_2
import BeaverStructural.BB7b.RuleR23_3
import BeaverStructural.BB7b.RuleR23_4
import BeaverStructural.BB7b.RuleR23_5
import BeaverStructural.BB7b.RuleR23_6
import BeaverStructural.BB7b.RuleR23_7
import BeaverStructural.BB7b.RuleR23_8
import BeaverStructural.BB7b.RuleR23_9
import BeaverStructural.BB7b.RuleR23_10
import BeaverStructural.BB7b.RuleR23_11
import BeaverStructural.BB7b.RuleR23_12
import BeaverStructural.BB7b.RuleR23_13
import BeaverStructural.BB7b.RuleR23_14
import BeaverStructural.BB7b.RuleR23_15
import BeaverStructural.BB7b.RuleR23_16
import BeaverStructural.BB7b.RuleR23_17
import BeaverStructural.BB7b.RuleR23_18
import BeaverStructural.BB7b.RuleR23_19

/-! The rules R23_k restated on the digit list of `kc`. -/

namespace BeaverStructural.BB7b

/-- R23_0 on the digit list: 0 zero digits, then the digit y + 1, with counter n + 0. -/
theorem step_R23_0 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (16 * n + 58) (kc ((y + 1) :: t) 0 (n + 0) h c) =
      kc (y :: t) (n + 3) 0 (h + (-4)) (c + (16 * n + 58)) :=
  rule_R23_0 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_1 on the digit list: 1 zero digits, then the digit y + 1, with counter n + 1. -/
theorem step_R23_1 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (24 * n + 102) (kc (0 :: (y + 1) :: t) 0 (n + 1) h c) =
      kc ((n + 3) :: y :: t) 1 0 (h + (-4)) (c + (24 * n + 102)) :=
  rule_R23_1 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_2 on the digit list: 2 zero digits, then the digit y + 1, with counter n + 2. -/
theorem step_R23_2 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (32 * n + 154) (kc (0 :: 0 :: (y + 1) :: t) 0 (n + 2) h c) =
      kc (1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (32 * n + 154)) :=
  rule_R23_2 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_3 on the digit list: 3 zero digits, then the digit y + 1, with counter n + 3. -/
theorem step_R23_3 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (40 * n + 214) (kc (0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 3) h c) =
      kc (1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (40 * n + 214)) :=
  rule_R23_3 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_4 on the digit list: 4 zero digits, then the digit y + 1, with counter n + 4. -/
theorem step_R23_4 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (48 * n + 282) (kc (0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 4) h c) =
      kc (1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (48 * n + 282)) :=
  rule_R23_4 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_5 on the digit list: 5 zero digits, then the digit y + 1, with counter n + 5. -/
theorem step_R23_5 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (56 * n + 358) (kc (0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 5) h c) =
      kc (1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (56 * n + 358)) :=
  rule_R23_5 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_6 on the digit list: 6 zero digits, then the digit y + 1, with counter n + 6. -/
theorem step_R23_6 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (64 * n + 442) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 6) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (64 * n + 442)) :=
  rule_R23_6 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_7 on the digit list: 7 zero digits, then the digit y + 1, with counter n + 7. -/
theorem step_R23_7 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (72 * n + 534) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 7) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (72 * n + 534)) :=
  rule_R23_7 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_8 on the digit list: 8 zero digits, then the digit y + 1, with counter n + 8. -/
theorem step_R23_8 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (80 * n + 634) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 8) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (80 * n + 634)) :=
  rule_R23_8 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_9 on the digit list: 9 zero digits, then the digit y + 1, with counter n + 9. -/
theorem step_R23_9 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (88 * n + 742) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 9) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (88 * n + 742)) :=
  rule_R23_9 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_10 on the digit list: 10 zero digits, then the digit y + 1, with counter n + 10. -/
theorem step_R23_10 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (96 * n + 858) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 10) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (96 * n + 858)) :=
  rule_R23_10 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_11 on the digit list: 11 zero digits, then the digit y + 1, with counter n + 11. -/
theorem step_R23_11 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (104 * n + 982) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 11) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (104 * n + 982)) :=
  rule_R23_11 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_12 on the digit list: 12 zero digits, then the digit y + 1, with counter n + 12. -/
theorem step_R23_12 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (112 * n + 1114) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 12) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (112 * n + 1114)) :=
  rule_R23_12 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_13 on the digit list: 13 zero digits, then the digit y + 1, with counter n + 13. -/
theorem step_R23_13 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (120 * n + 1254) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 13) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (120 * n + 1254)) :=
  rule_R23_13 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_14 on the digit list: 14 zero digits, then the digit y + 1, with counter n + 14. -/
theorem step_R23_14 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (128 * n + 1402) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 14) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (128 * n + 1402)) :=
  rule_R23_14 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_15 on the digit list: 15 zero digits, then the digit y + 1, with counter n + 15. -/
theorem step_R23_15 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (136 * n + 1558) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 15) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (136 * n + 1558)) :=
  rule_R23_15 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_16 on the digit list: 16 zero digits, then the digit y + 1, with counter n + 16. -/
theorem step_R23_16 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (144 * n + 1722) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 16) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (144 * n + 1722)) :=
  rule_R23_16 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_17 on the digit list: 17 zero digits, then the digit y + 1, with counter n + 17. -/
theorem step_R23_17 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (152 * n + 1894) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 17) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (152 * n + 1894)) :=
  rule_R23_17 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_18 on the digit list: 18 zero digits, then the digit y + 1, with counter n + 18. -/
theorem step_R23_18 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (160 * n + 2074) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 18) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (160 * n + 2074)) :=
  rule_R23_18 n (ones (2 * y) ++ false :: false :: rgt t) h c

/-- R23_19 on the digit list: 19 zero digits, then the digit y + 1, with counter n + 19. -/
theorem step_R23_19 (n y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (168 * n + 2262) (kc (0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: (y + 1) :: t) 0 (n + 19) h c) =
      kc (1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: (n + 3) :: y :: t) 1 0 (h + (-4)) (c + (168 * n + 2262)) :=
  rule_R23_19 n (ones (2 * y) ++ false :: false :: rgt t) h c

end BeaverStructural.BB7b

