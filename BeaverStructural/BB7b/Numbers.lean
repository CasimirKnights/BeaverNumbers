import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring

/-! The numbers of the BB(7) machine of October 2026: the maps V_0(x) = 3x + 3, s_0 = 1, s_(k+1) = V_k(s_k),
V_(k+1)(x) = V_k^(3x+2−k)(s_k); the rule costs; the clock T_k(n, a) of clearing n units at position k and the clock
P_k of clearing k digits 1; the ladder Acc_0 = 8, Acc_(i+1) = V_(i+1)(Acc_i); the step count τ and the score σ. -/

namespace BeaverStructural.BB7b

open Finset

/-- The pair (V_k, s_k). -/
def VS : ℕ → (ℕ → ℕ) × ℕ
  | 0 => (fun x => 3 * x + 3, 1)
  | k + 1 => (fun x => ((VS k).1)^[3 * x + 2 - k] (VS k).2, (VS k).1 (VS k).2)

def V (k : ℕ) : ℕ → ℕ := (VS k).1

def s (k : ℕ) : ℕ := (VS k).2

theorem V_zero (x : ℕ) : V 0 x = 3 * x + 3 := rfl

theorem s_zero : s 0 = 1 := rfl

theorem V_succ (k x : ℕ) : V (k + 1) x = (V k)^[3 * x + 2 - k] (s k) := rfl

theorem s_succ (k : ℕ) : s (k + 1) = V k (s k) := rfl

/-- Rule D at accumulator a. -/
def cD (a : ℕ) : ℕ := 12 * a * a + 66 * a + 58

/-- The sweep, the turn and the return with k zero digits and counter n + k. -/
def costB (k n : ℕ) : ℕ := 8 * (k + 2) * n + (4 * k * k + 40 * k + 58)

/-- Rule B_k at accumulator a (k ≤ 3a): the mini-cycles, then the sweep with counter 3a. -/
def cB (a k : ℕ) : ℕ := 12 * a * a + 18 * a + costB k (3 * a - k)

/-- Rule E with twenty zero digits at accumulator m + 7, the halting row included. -/
def costE (m : ℕ) : ℕ := 48 * m * m + 870 * m + 3282

theorem costE_eq (m : ℕ) : costE m + 30 * 20 = 48 * (m + 7) * (m + 7) + 198 * (m + 7) + 144 := by
  unfold costE; ring

/-- The pair (T_k, P_k). -/
def TP : ℕ → (ℕ → ℕ → ℕ) × ℕ
  | 0 => (fun n a => ∑ i ∈ range n, cD ((V 0)^[i] a), 0)
  | k + 1 =>
    (fun n a => ∑ i ∈ range n,
        (cB ((V (k + 1))^[i] a) (k + 1) + (TP k).2 + (TP k).1 (3 * ((V (k + 1))^[i] a) + 2 - k) (s k)),
      (TP k).2 + (TP k).1 1 (s k))

/-- `T k n a`: the steps from K(a; 0^k, n, rest) to K(V_k^n(a); 0^k, 0, rest). -/
def T (k : ℕ) : ℕ → ℕ → ℕ := (TP k).1

/-- `P k`: the steps from K(1; 1^k, rest) to K(s_k; 0^k, rest). -/
def P (k : ℕ) : ℕ := (TP k).2

theorem P_zero : P 0 = 0 := rfl

theorem P_succ (k : ℕ) : P (k + 1) = P k + T k 1 (s k) := rfl

theorem T_none (k a : ℕ) : T k 0 a = 0 := by
  cases k with
  | zero => show ∑ i ∈ range 0, cD ((V 0)^[i] a) = 0; simp
  | succ k =>
    show ∑ i ∈ range 0,
      (cB ((V (k + 1))^[i] a) (k + 1) + P k + T k (3 * ((V (k + 1))^[i] a) + 2 - k) (s k)) = 0
    simp

theorem T_zero_succ (n a : ℕ) : T 0 (n + 1) a = cD a + T 0 n (V 0 a) := by
  show ∑ i ∈ range (n + 1), cD ((V 0)^[i] a) = cD a + ∑ i ∈ range n, cD ((V 0)^[i] (V 0 a))
  rw [sum_range_succ']
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  ring

theorem T_succ_succ (k n a : ℕ) :
    T (k + 1) (n + 1) a =
      (cB a (k + 1) + P k + T k (3 * a + 2 - k) (s k)) + T (k + 1) n (V (k + 1) a) := by
  show ∑ i ∈ range (n + 1),
      (cB ((V (k + 1))^[i] a) (k + 1) + P k + T k (3 * ((V (k + 1))^[i] a) + 2 - k) (s k)) =
    (cB a (k + 1) + P k + T k (3 * a + 2 - k) (s k)) +
      ∑ i ∈ range n, (cB ((V (k + 1))^[i] (V (k + 1) a)) (k + 1) + P k +
        T k (3 * ((V (k + 1))^[i] (V (k + 1) a)) + 2 - k) (s k))
  rw [sum_range_succ']
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  ring

theorem iter_ge (f : ℕ → ℕ) (hf : ∀ y, y + 1 ≤ f y) (m z : ℕ) : z + m ≤ f^[m] z := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have := hf (f^[m] z)
    omega

theorem V_s_bounds (k : ℕ) : (∀ y, y + 1 ≤ V k y) ∧ k + 1 ≤ s k := by
  induction k with
  | zero => exact ⟨fun y => by rw [V_zero]; omega, by rw [s_zero]⟩
  | succ k ih =>
    obtain ⟨hV, hs⟩ := ih
    have hs' : k + 1 + 1 ≤ s (k + 1) := by
      rw [s_succ]
      have := hV (s k)
      omega
    refine ⟨fun y => ?_, hs'⟩
    rw [V_succ]
    have := iter_ge (V k) hV (3 * y + 2 - k) (s k)
    omega

theorem V_ge (k y : ℕ) : y + 1 ≤ V k y := (V_s_bounds k).1 y

theorem s_ge (k : ℕ) : k + 1 ≤ s k := (V_s_bounds k).2

/-- The ladder: the accumulator before the digit at position i + 1 is cleared. -/
def Acc : ℕ → ℕ
  | 0 => 8
  | i + 1 => V (i + 1) (Acc i)

theorem Acc_ge (i : ℕ) : 8 + i ≤ Acc i := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    show 8 + (i + 1) ≤ V (i + 1) (Acc i)
    have := V_ge (i + 1) (Acc i)
    omega

/-- The step count from the blank tape, the halting row included. -/
def tau : ℕ := 3959 + ∑ i ∈ range 19, T (i + 1) 1 (Acc i) + costE (Acc 19 - 7)

/-- The number of ones on the halted tape. -/
def sigma : ℕ := 6 * Acc 19 + 7

/-- τ's body over a variable ladder, at the definitional height of τ. -/
def tauF (Af : ℕ → ℕ) : ℕ :=
  (fun _ : ℕ → ℕ => 3959 + ∑ i ∈ range 19, T (i + 1) 1 (Af i) + costE (Af 19 - 7)) Acc

/-- σ's body over a variable, at the definitional height of σ. -/
def sigF (a : ℕ) : ℕ := (fun _ : ℕ → ℕ => 6 * a + 7) Acc

theorem tau_tauF : tau = tauF Acc := rfl

theorem tauF_eq (Af : ℕ → ℕ) : tauF Af = 3959 + ∑ i ∈ range 19, T (i + 1) 1 (Af i) + costE (Af 19 - 7) := rfl

theorem sigma_sigF : sigma = sigF (Acc 19) := rfl

theorem sigF_eq (a : ℕ) : sigF a = 6 * a + 7 := rfl

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.V_s_bounds
#print axioms BeaverStructural.BB7b.T_succ_succ
