import BeaverStructural.BB7b.Macro
import BeaverStructural.BB7b.Numbers
import Mathlib.Tactic.IntervalCases

/-! The high-level rule of the BB(7) machine of October 2026, every position k ≤ 19:
K(a; 0^k, n, rest) → K(V_k^n(a); 0^k, 0, rest) in T_k(n, a) steps, and K(1; 1^k, rest) → K(s_k; 0^k, rest) in P_k
steps, by induction on k then n from the macro rules D and B_k. -/

namespace BeaverStructural.BB7b

open Finset

theorem replicate_succ_append (k v : ℕ) (X : List ℕ) :
    List.replicate (k + 1) v ++ X = List.replicate k v ++ v :: X := by
  rw [List.replicate_succ', List.append_assoc]; rfl

/-- Rule D with the clock's cost. -/
theorem macroD (a y : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (cD a) (kc ((y + 1) :: t) a 0 h c) =
      kc (y :: t) (V 0 a) 0 (h - 4 * (a : ℤ) + (-4)) (c + cD a) := by
  have r := rule_D a (3 * a) y t (by omega) h c
  refine (congrArg (fun k => Zip.run k _)
    (show cD a = 12 * a * a + 18 * a + (16 * (3 * a) + 58) by unfold cD; ring)).trans (r.trans ?_)
  exact zip_eq rfl rfl rfl rfl (by unfold cD; ring)

/-- Rule B_k with the clock's cost, 1 ≤ k ≤ 19. -/
theorem macroB (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 19) (a y : ℕ) (t : List ℕ) (ha : k ≤ 3 * a) (h : ℤ) (c : ℕ) :
    Zip.run (cB a k) (kc (List.replicate k 0 ++ (y + 1) :: t) a 0 h c) =
      kc (List.replicate (k - 1) 1 ++ (3 * a - k + 3) :: y :: t) 1 0 (h - 4 * (a : ℤ) + (-4)) (c + cB a k) := by
  have hn : 3 * a = (3 * a - k) + k := by omega
  unfold cB
  generalize 3 * a - k = n at hn ⊢
  interval_cases k
  · exact rule_B_1 a n y t hn h c
  · exact rule_B_2 a n y t hn h c
  · exact rule_B_3 a n y t hn h c
  · exact rule_B_4 a n y t hn h c
  · exact rule_B_5 a n y t hn h c
  · exact rule_B_6 a n y t hn h c
  · exact rule_B_7 a n y t hn h c
  · exact rule_B_8 a n y t hn h c
  · exact rule_B_9 a n y t hn h c
  · exact rule_B_10 a n y t hn h c
  · exact rule_B_11 a n y t hn h c
  · exact rule_B_12 a n y t hn h c
  · exact rule_B_13 a n y t hn h c
  · exact rule_B_14 a n y t hn h c
  · exact rule_B_15 a n y t hn h c
  · exact rule_B_16 a n y t hn h c
  · exact rule_B_17 a n y t hn h c
  · exact rule_B_18 a n y t hn h c
  · exact rule_B_19 a n y t hn h c

/-- The high-level rule and the clearing of k digits 1, every k ≤ 19. -/
theorem high (k : ℕ) (hk : k ≤ 19) :
    (∀ (n a : ℕ) (t : List ℕ) (h : ℤ) (c : ℕ), k ≤ 3 * a → ∃ h' : ℤ,
      Zip.run (T k n a) (kc (List.replicate k 0 ++ n :: t) a 0 h c) =
        kc (List.replicate k 0 ++ 0 :: t) ((V k)^[n] a) 0 h' (c + T k n a)) ∧
    (∀ (t : List ℕ) (h : ℤ) (c : ℕ), ∃ h' : ℤ,
      Zip.run (P k) (kc (List.replicate k 1 ++ t) 1 0 h c) =
        kc (List.replicate k 0 ++ t) (s k) 0 h' (c + P k)) := by
  induction k with
  | zero =>
    refine ⟨?_, fun t h c => ⟨h, by simp [P_zero, Zip.run, s_zero]⟩⟩
    intro n
    induction n with
    | zero => intro a t h c _; exact ⟨h, by simp [T_none, Zip.run]⟩
    | succ n ih =>
      intro a t h c _
      obtain ⟨h', e⟩ := ih (V 0 a) t (h - 4 * (a : ℤ) + (-4)) (c + cD a) (by omega)
      refine ⟨h', ?_⟩
      have m := macroD a n t h c
      simp only [List.replicate_zero, List.nil_append] at e ⊢
      rw [T_zero_succ, Zip.run_add, m, e, Function.iterate_succ_apply]
      exact zip_eq rfl rfl rfl rfl (by ring)
  | succ k ihk =>
    obtain ⟨Ck, Pk⟩ := ihk (by omega)
    have Pk1 : ∀ (t : List ℕ) (h : ℤ) (c : ℕ), ∃ h' : ℤ,
        Zip.run (P (k + 1)) (kc (List.replicate (k + 1) 1 ++ t) 1 0 h c) =
          kc (List.replicate (k + 1) 0 ++ t) (s (k + 1)) 0 h' (c + P (k + 1)) := by
      intro t h c
      obtain ⟨h1, e1⟩ := Pk (1 :: t) h c
      obtain ⟨h2, e2⟩ := Ck 1 (s k) t h1 (c + P k) (by have := s_ge k; omega)
      refine ⟨h2, ?_⟩
      rw [replicate_succ_append k 1 t, P_succ, Zip.run_add, e1, e2, replicate_succ_append k 0 t]
      exact zip_eq rfl rfl rfl rfl (by ring)
    refine ⟨?_, Pk1⟩
    intro n
    induction n with
    | zero => intro a t h c _; exact ⟨h, by simp [T_none, Zip.run]⟩
    | succ n ih =>
      intro a t h c ha
      have hd : 3 * a - (k + 1) + 3 = 3 * a + 2 - k := by omega
      have m := macroB (k + 1) (by omega) hk a n t ha h c
      rw [Nat.add_sub_cancel, hd] at m
      obtain ⟨h1, e1⟩ := Pk ((3 * a + 2 - k) :: n :: t) (h - 4 * (a : ℤ) + (-4)) (c + cB a (k + 1))
      obtain ⟨h2, e2⟩ := Ck (3 * a + 2 - k) (s k) (n :: t) h1 (c + cB a (k + 1) + P k)
        (by have := s_ge k; omega)
      obtain ⟨h3, e3⟩ := ih (V (k + 1) a) t h2 (c + cB a (k + 1) + P k + T k (3 * a + 2 - k) (s k))
        (by have := V_ge (k + 1) a; omega)
      refine ⟨h3, ?_⟩
      rw [T_succ_succ, Zip.run_add, Zip.run_add, Zip.run_add, m, e1, e2,
        show (V k)^[3 * a + 2 - k] (s k) = V (k + 1) a from rfl, ← replicate_succ_append k 0 (n :: t), e3,
        Function.iterate_succ_apply]
      exact zip_eq rfl rfl rfl rfl (by ring)

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.high
