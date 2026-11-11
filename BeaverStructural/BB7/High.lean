import BeaverStructural.BB7.Mid2
import BeaverStructural.BB7.RulesR4_12
/-! The high-level rule B(a; [0]*k, n, rest) → B(g_k^n(a); [0]*k, 0, rest) in T_k(n, a) steps (k ≤ 12), by induction on k
then n, from the two mid-level rules; and the halting mid-level rule B(a; [0]*12) → halt in CH(a, 12) steps. -/

namespace BeaverStructural.BB7

open Finset

theorem T_zero_succ (n a : ℕ) : T 0 (n + 1) a = C1 a + T 0 n (g 0 a) := by
  simp only [T]
  rw [sum_range_succ']
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  ring

theorem T_succ_succ (k n a : ℕ) :
    T (k + 1) (n + 1) a = (C2 a k + T k (a + 2) 0) + T (k + 1) n (g (k + 1) a) := by
  simp only [T]
  rw [sum_range_succ']
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  ring

theorem replicate_succ_append (k : ℕ) (X : List ℕ) :
    List.replicate (k + 1) 0 ++ X = List.replicate k 0 ++ 0 :: X := by
  rw [List.replicate_succ', List.append_assoc]; rfl

/-- The high-level rule, every k ≤ 12. -/
theorem high (k : ℕ) (hk : k ≤ 12) : ∀ (n a : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ), ∃ h' : ℤ,
    Zip.run (T k n a) (bZip a (List.replicate k 0 ++ n :: rest) h c) =
      bZip ((g k)^[n] a) (List.replicate k 0 ++ 0 :: rest) h' (c + T k n a) := by
  induction k with
  | zero =>
    intro n
    induction n with
    | zero => intro a rest h c; exact ⟨h, by simp [T, Zip.run]⟩
    | succ n ih =>
      intro a rest h c
      obtain ⟨h', e⟩ := ih (g 0 a) rest (h + (6 * a + 18)) (c + C1 a)
      refine ⟨h', ?_⟩
      have m := mid1 a n rest h c
      simp only [List.replicate_zero, List.nil_append] at e ⊢
      rw [T_zero_succ, Zip.run_add, m, show 2 * a + 4 = g 0 a from rfl, e, Function.iterate_succ_apply]
      exact zip_eq rfl rfl rfl rfl (by ring)
  | succ k ihk =>
    intro n
    induction n with
    | zero => intro a rest h c; exact ⟨h, by simp [T, Zip.run]⟩
    | succ n ih =>
      intro a rest h c
      have m := mid2 k a n rest h c (by omega)
      obtain ⟨h1, e1⟩ := ihk (by omega) (a + 2) 0 (n :: rest) (h + 6) (c + C2 a k)
      obtain ⟨h2, e2⟩ := ih (g (k + 1) a) rest h1 (c + C2 a k + T k (a + 2) 0)
      refine ⟨h2, ?_⟩
      rw [replicate_succ_append k ((n + 1) :: rest), T_succ_succ, Zip.run_add, Zip.run_add, m, e1,
        show (g k)^[a + 2] 0 = g (k + 1) a from rfl, ← replicate_succ_append k (n :: rest), e2,
        Function.iterate_succ_apply]
      exact zip_eq rfl rfl rfl rfl (by ring)

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.high
