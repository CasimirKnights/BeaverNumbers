import BeaverStructural.BB7.Mid
import BeaverStructural.BB7.RulesR3_0
import BeaverStructural.BB7.RulesR3_1
import BeaverStructural.BB7.RulesR3_2
import BeaverStructural.BB7.RulesR3_3
import BeaverStructural.BB7.RulesR3_4
import BeaverStructural.BB7.RulesR3_5
import BeaverStructural.BB7.RulesR3_6
import BeaverStructural.BB7.RulesR3_7
import BeaverStructural.BB7.RulesR3_8
import BeaverStructural.BB7.RulesR3_9
import BeaverStructural.BB7.RulesR3_10
import BeaverStructural.BB7.RulesR3_11
import Mathlib.Tactic.IntervalCases

/-! B(a; [0]*k, 0, n+1, rest) → B(0; [0]*k, a+2, n, rest) in C2(a, k) steps, k ≤ 11, each one R3_k at n = 3a + 1. -/

namespace BeaverStructural.BB7

set_option maxRecDepth 8000 in
theorem mid2_0 (a n : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (C2 a 0) (bZip a (List.replicate 0 0 ++ 0 :: (n + 1) :: rest) h c) =
      bZip 0 (List.replicate 0 0 ++ (a + 2) :: n :: rest) (h + 6) (c + C2 a 0) := by
  have e := rule_R3_0 (3 * a + 1) (pw true false (3 * n + 1) ++ true :: blk rest) h c
  unfold bZip
  convert e using 2
  all_goals first
    | (simp only [C2]; ring)
    | (simp [bLeft, blk, blk_zeros, pw_three_succ, List.replicate_succ]; done)
    | (simp only [Zip.mk.injEq, true_and]
       refine ⟨?_, rfl, by simp only [C2]; ring⟩
       simp [bLeft, blk, blk_zeros, List.replicate_succ]
       rw [show 3 * (a + 2) + 1 = 3 * a + 1 + 6 by ring])

set_option maxRecDepth 8000 in
theorem mid2_1 (a n : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (C2 a 1) (bZip a (List.replicate 1 0 ++ 0 :: (n + 1) :: rest) h c) =
      bZip 0 (List.replicate 1 0 ++ (a + 2) :: n :: rest) (h + 6) (c + C2 a 1) := by
  have e := rule_R3_1 (3 * a + 1) (pw true false (3 * n + 1) ++ true :: blk rest) h c
  unfold bZip
  convert e using 2
  all_goals first
    | (simp only [C2]; ring)
    | (simp [bLeft, blk, blk_zeros, pw_three_succ, List.replicate_succ]; done)
    | (simp only [Zip.mk.injEq, true_and]
       refine ⟨?_, rfl, by simp only [C2]; ring⟩
       simp [bLeft, blk, blk_zeros, List.replicate_succ]
       rw [show 3 * (a + 2) + 1 = 3 * a + 1 + 6 by ring])

set_option maxRecDepth 8000 in
theorem mid2_2 (a n : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (C2 a 2) (bZip a (List.replicate 2 0 ++ 0 :: (n + 1) :: rest) h c) =
      bZip 0 (List.replicate 2 0 ++ (a + 2) :: n :: rest) (h + 6) (c + C2 a 2) := by
  have e := rule_R3_2 (3 * a + 1) (pw true false (3 * n + 1) ++ true :: blk rest) h c
  unfold bZip
  convert e using 2
  all_goals first
    | (simp only [C2]; ring)
    | (simp [bLeft, blk, blk_zeros, pw_three_succ, List.replicate_succ]; done)
    | (simp only [Zip.mk.injEq, true_and]
       refine ⟨?_, rfl, by simp only [C2]; ring⟩
       simp [bLeft, blk, blk_zeros, List.replicate_succ]
       rw [show 3 * (a + 2) + 1 = 3 * a + 1 + 6 by ring])

set_option maxRecDepth 8000 in
theorem mid2_3 (a n : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (C2 a 3) (bZip a (List.replicate 3 0 ++ 0 :: (n + 1) :: rest) h c) =
      bZip 0 (List.replicate 3 0 ++ (a + 2) :: n :: rest) (h + 6) (c + C2 a 3) := by
  have e := rule_R3_3 (3 * a + 1) (pw true false (3 * n + 1) ++ true :: blk rest) h c
  unfold bZip
  convert e using 2
  all_goals first
    | (simp only [C2]; ring)
    | (simp [bLeft, blk, blk_zeros, pw_three_succ, List.replicate_succ]; done)
    | (simp only [Zip.mk.injEq, true_and]
       refine ⟨?_, rfl, by simp only [C2]; ring⟩
       simp [bLeft, blk, blk_zeros, List.replicate_succ]
       rw [show 3 * (a + 2) + 1 = 3 * a + 1 + 6 by ring])

set_option maxRecDepth 8000 in
theorem mid2_4 (a n : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (C2 a 4) (bZip a (List.replicate 4 0 ++ 0 :: (n + 1) :: rest) h c) =
      bZip 0 (List.replicate 4 0 ++ (a + 2) :: n :: rest) (h + 6) (c + C2 a 4) := by
  have e := rule_R3_4 (3 * a + 1) (pw true false (3 * n + 1) ++ true :: blk rest) h c
  unfold bZip
  convert e using 2
  all_goals first
    | (simp only [C2]; ring)
    | (simp [bLeft, blk, blk_zeros, pw_three_succ, List.replicate_succ]; done)
    | (simp only [Zip.mk.injEq, true_and]
       refine ⟨?_, rfl, by simp only [C2]; ring⟩
       simp [bLeft, blk, blk_zeros, List.replicate_succ]
       rw [show 3 * (a + 2) + 1 = 3 * a + 1 + 6 by ring])

set_option maxRecDepth 8000 in
theorem mid2_5 (a n : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (C2 a 5) (bZip a (List.replicate 5 0 ++ 0 :: (n + 1) :: rest) h c) =
      bZip 0 (List.replicate 5 0 ++ (a + 2) :: n :: rest) (h + 6) (c + C2 a 5) := by
  have e := rule_R3_5 (3 * a + 1) (pw true false (3 * n + 1) ++ true :: blk rest) h c
  unfold bZip
  convert e using 2
  all_goals first
    | (simp only [C2]; ring)
    | (simp [bLeft, blk, blk_zeros, pw_three_succ, List.replicate_succ]; done)
    | (simp only [Zip.mk.injEq, true_and]
       refine ⟨?_, rfl, by simp only [C2]; ring⟩
       simp [bLeft, blk, blk_zeros, List.replicate_succ]
       rw [show 3 * (a + 2) + 1 = 3 * a + 1 + 6 by ring])

set_option maxRecDepth 8000 in
theorem mid2_6 (a n : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (C2 a 6) (bZip a (List.replicate 6 0 ++ 0 :: (n + 1) :: rest) h c) =
      bZip 0 (List.replicate 6 0 ++ (a + 2) :: n :: rest) (h + 6) (c + C2 a 6) := by
  have e := rule_R3_6 (3 * a + 1) (pw true false (3 * n + 1) ++ true :: blk rest) h c
  unfold bZip
  convert e using 2
  all_goals first
    | (simp only [C2]; ring)
    | (simp [bLeft, blk, blk_zeros, pw_three_succ, List.replicate_succ]; done)
    | (simp only [Zip.mk.injEq, true_and]
       refine ⟨?_, rfl, by simp only [C2]; ring⟩
       simp [bLeft, blk, blk_zeros, List.replicate_succ]
       rw [show 3 * (a + 2) + 1 = 3 * a + 1 + 6 by ring])

set_option maxRecDepth 8000 in
theorem mid2_7 (a n : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (C2 a 7) (bZip a (List.replicate 7 0 ++ 0 :: (n + 1) :: rest) h c) =
      bZip 0 (List.replicate 7 0 ++ (a + 2) :: n :: rest) (h + 6) (c + C2 a 7) := by
  have e := rule_R3_7 (3 * a + 1) (pw true false (3 * n + 1) ++ true :: blk rest) h c
  unfold bZip
  convert e using 2
  all_goals first
    | (simp only [C2]; ring)
    | (simp [bLeft, blk, blk_zeros, pw_three_succ, List.replicate_succ]; done)
    | (simp only [Zip.mk.injEq, true_and]
       refine ⟨?_, rfl, by simp only [C2]; ring⟩
       simp [bLeft, blk, blk_zeros, List.replicate_succ]
       rw [show 3 * (a + 2) + 1 = 3 * a + 1 + 6 by ring])

set_option maxRecDepth 8000 in
theorem mid2_8 (a n : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (C2 a 8) (bZip a (List.replicate 8 0 ++ 0 :: (n + 1) :: rest) h c) =
      bZip 0 (List.replicate 8 0 ++ (a + 2) :: n :: rest) (h + 6) (c + C2 a 8) := by
  have e := rule_R3_8 (3 * a + 1) (pw true false (3 * n + 1) ++ true :: blk rest) h c
  unfold bZip
  convert e using 2
  all_goals first
    | (simp only [C2]; ring)
    | (simp [bLeft, blk, blk_zeros, pw_three_succ, List.replicate_succ]; done)
    | (simp only [Zip.mk.injEq, true_and]
       refine ⟨?_, rfl, by simp only [C2]; ring⟩
       simp [bLeft, blk, blk_zeros, List.replicate_succ]
       rw [show 3 * (a + 2) + 1 = 3 * a + 1 + 6 by ring])

set_option maxRecDepth 8000 in
theorem mid2_9 (a n : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (C2 a 9) (bZip a (List.replicate 9 0 ++ 0 :: (n + 1) :: rest) h c) =
      bZip 0 (List.replicate 9 0 ++ (a + 2) :: n :: rest) (h + 6) (c + C2 a 9) := by
  have e := rule_R3_9 (3 * a + 1) (pw true false (3 * n + 1) ++ true :: blk rest) h c
  unfold bZip
  convert e using 2
  all_goals first
    | (simp only [C2]; ring)
    | (simp [bLeft, blk, blk_zeros, pw_three_succ, List.replicate_succ]; done)
    | (simp only [Zip.mk.injEq, true_and]
       refine ⟨?_, rfl, by simp only [C2]; ring⟩
       simp [bLeft, blk, blk_zeros, List.replicate_succ]
       rw [show 3 * (a + 2) + 1 = 3 * a + 1 + 6 by ring])

set_option maxRecDepth 8000 in
theorem mid2_10 (a n : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (C2 a 10) (bZip a (List.replicate 10 0 ++ 0 :: (n + 1) :: rest) h c) =
      bZip 0 (List.replicate 10 0 ++ (a + 2) :: n :: rest) (h + 6) (c + C2 a 10) := by
  have e := rule_R3_10 (3 * a + 1) (pw true false (3 * n + 1) ++ true :: blk rest) h c
  unfold bZip
  convert e using 2
  all_goals first
    | (simp only [C2]; ring)
    | (simp [bLeft, blk, blk_zeros, pw_three_succ, List.replicate_succ]; done)
    | (simp only [Zip.mk.injEq, true_and]
       refine ⟨?_, rfl, by simp only [C2]; ring⟩
       simp [bLeft, blk, blk_zeros, List.replicate_succ]
       rw [show 3 * (a + 2) + 1 = 3 * a + 1 + 6 by ring])

set_option maxRecDepth 8000 in
theorem mid2_11 (a n : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (C2 a 11) (bZip a (List.replicate 11 0 ++ 0 :: (n + 1) :: rest) h c) =
      bZip 0 (List.replicate 11 0 ++ (a + 2) :: n :: rest) (h + 6) (c + C2 a 11) := by
  have e := rule_R3_11 (3 * a + 1) (pw true false (3 * n + 1) ++ true :: blk rest) h c
  unfold bZip
  convert e using 2
  all_goals first
    | (simp only [C2]; ring)
    | (simp [bLeft, blk, blk_zeros, pw_three_succ, List.replicate_succ]; done)
    | (simp only [Zip.mk.injEq, true_and]
       refine ⟨?_, rfl, by simp only [C2]; ring⟩
       simp [bLeft, blk, blk_zeros, List.replicate_succ]
       rw [show 3 * (a + 2) + 1 = 3 * a + 1 + 6 by ring])

/-- The second mid-level rule for every k ≤ 11. -/
theorem mid2 (k a n : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) (hk : k ≤ 11) :
    Zip.run (C2 a k) (bZip a (List.replicate k 0 ++ 0 :: (n + 1) :: rest) h c) =
      bZip 0 (List.replicate k 0 ++ (a + 2) :: n :: rest) (h + 6) (c + C2 a k) := by
  interval_cases k
  · exact mid2_0 a n rest h c
  · exact mid2_1 a n rest h c
  · exact mid2_2 a n rest h c
  · exact mid2_3 a n rest h c
  · exact mid2_4 a n rest h c
  · exact mid2_5 a n rest h c
  · exact mid2_6 a n rest h c
  · exact mid2_7 a n rest h c
  · exact mid2_8 a n rest h c
  · exact mid2_9 a n rest h c
  · exact mid2_10 a n rest h c
  · exact mid2_11 a n rest h c

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.mid2
