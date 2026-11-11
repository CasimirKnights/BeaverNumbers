import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

/-! The BB(7) champion's numbers: the g-hierarchy g₀(x) = 2x + 4, g_(k+1)(x) = g_k^(x+2)(0); Knuth's arrows
2↑^k y with 2↑^0 y = 2y; the rule costs R1–R4, C1, C2, CH; the high-level clock T_k(n, a); the ladder A₀ = 4,
A_(j+1) = g_j(A_j); the step count τ = 8574 + Σ_(j<12) T_j(1, A_j) + CH(A₁₂, 12) and the score σ = 3·A₁₂ + 34.
`g_eq_arrow`: g_k(x) = 2↑^k(x + 4) − 4. -/

namespace BeaverStructural.BB7

open Finset

/-- The g-hierarchy. -/
def g : ℕ → ℕ → ℕ
  | 0, x => 2 * x + 4
  | k + 1, x => (g k)^[x + 2] 0

/-- Knuth's arrows with base 2: `arrow k y = 2↑^k y`, `2↑^0 y = 2y`. -/
def arrow : ℕ → ℕ → ℕ
  | 0, y => 2 * y
  | k + 1, y => (arrow k)^[y] 1

theorem arrow_succ_zero (k : ℕ) : arrow (k + 1) 0 = 1 := rfl

theorem arrow_succ_succ (k y : ℕ) : arrow (k + 1) (y + 1) = arrow k (arrow (k + 1) y) := by
  simp only [arrow]
  rw [Function.iterate_succ_apply']

def R1 (n : ℕ) : ℕ := 4 * n + 42
def R2 (n : ℕ) : ℕ := 16 * n + 178
def R3 (k n : ℕ) : ℕ := (24 + 8 * k) * n + 226 + 48 * k
def R4 (k n : ℕ) : ℕ := (2 + 8 * k) * n + 27 + 21 * k
def C1 (a : ℕ) : ℕ := 36 * a ^ 2 + 318 * a + 590
def C2 (a k : ℕ) : ℕ := (24 + 8 * k) * (3 * a + 1) + 226 + 48 * k
def CH (a k : ℕ) : ℕ := (2 + 8 * k) * (3 * a + 1) + 27 + 21 * k

/-- The high-level clock: `T k n a` is the cost of B(a; [0]*k, n, rest) → B(g_k^n(a); [0]*k, 0, rest). -/
def T : ℕ → ℕ → ℕ → ℕ
  | 0, n, a => ∑ i ∈ range n, C1 ((g 0)^[i] a)
  | k + 1, n, a => ∑ i ∈ range n, (C2 ((g (k + 1))^[i] a) k + T k ((g (k + 1))^[i] a + 2) 0)

/-- The ladder A₀ = 4, A_(j+1) = g_j(A_j). -/
def A : ℕ → ℕ
  | 0 => 4
  | j + 1 => g j (A j)

/-- The step count of the champion from the blank tape, the halting row included. -/
def tau : ℕ := 8574 + ∑ j ∈ range 12, T j 1 (A j) + CH (A 12) 12

/-- The number of ones on the tape after the halting row. -/
def sigma : ℕ := 3 * A 12 + 34

theorem arrow_one (k : ℕ) : arrow k 1 = 2 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [arrow_succ_succ, arrow_succ_zero, ih]

theorem arrow_two (k : ℕ) : arrow k 2 = 4 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [arrow_succ_succ, arrow_one, ih]

theorem arrow_ge (k y : ℕ) (hy : 2 ≤ y) : 4 ≤ arrow k y := by
  induction k generalizing y with
  | zero => simp only [arrow]; omega
  | succ k ih =>
    obtain ⟨m, rfl⟩ : ∃ m, y = m + 2 := ⟨y - 2, by omega⟩
    induction m with
    | zero => rw [arrow_two]
    | succ m ihm =>
      rw [show m + 1 + 2 = (m + 2) + 1 by ring, arrow_succ_succ]
      exact ih _ (by have := ihm (by omega); omega)

/-- g_k(x) = 2↑^k(x + 4) − 4. -/
theorem g_eq_arrow (k x : ℕ) : g k x = arrow k (x + 4) - 4 := by
  induction k generalizing x with
  | zero => simp [g, arrow]; omega
  | succ k ih =>
    have hit : ∀ m, (g k)^[m] 0 = arrow (k + 1) (m + 2) - 4 := by
      intro m
      induction m with
      | zero => simp [arrow_two]
      | succ m ihm =>
        rw [Function.iterate_succ_apply', ihm, ih, Nat.sub_add_cancel (arrow_ge _ _ (by omega)),
          show m + 1 + 2 = (m + 2) + 1 by ring, ← arrow_succ_succ]
    rw [g, hit]

theorem A_one : A 1 = 12 := rfl
theorem A_two : A 2 = 65532 := by
  show g 1 12 = 65532
  rw [g_eq_arrow]
  decide

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.g_eq_arrow
#print axioms BeaverStructural.BB7.A_two
