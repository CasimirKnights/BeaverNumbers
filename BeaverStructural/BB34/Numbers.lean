import BeaverStructural.BB7.Defs

/-! The numbers of the BB(3,4) machine.  The configuration B(k, n, a) is 0^∞ 3^(a+1) 2^k A> 1^n (a is twice Ligocki's
m).  At k = 1 a unit costs 4a + 9 steps and adds 2 to a: n units cost `W1 n a` = n(4a + 4n + 5).  At k = j + 2 a unit
sends a to g_j(a), g the hierarchy g₀(x) = 2x + 4, g_(j+1)(x) = g_j^(x+2)(0) of `BB7.Defs`, and n units cost
`T j n a`: T_0 has summand C1(a) = 5a + 11 + W1(a + 2, 0), T_(j+1) has summand C2(a, j) + T_j(a + 2, 0).
The blank tape reaches B(16, 3, 0) with right context 2 at step 241, and A2 halts: τ = 241 + T_14(3, 0) + 1,
σ = g_14^3(0) + 18. -/

namespace BeaverStructural.BB34

open Finset
open BeaverStructural.BB7 (g)

/-- n units at k = 1 from accumulator a. -/
def W1 (n a : ℕ) : ℕ := n * (4 * a + 4 * n + 5)

theorem W1_succ (n a : ℕ) : W1 (n + 1) a = (4 * a + 9) + W1 n (a + 2) := by unfold W1; ring

/-- One unit at k = 2. -/
def C1 (a : ℕ) : ℕ := 4 * a ^ 2 + 26 * a + 37

theorem C1_eq (a : ℕ) : C1 a = (2 * 0 + 5) * a + 4 * 0 + 11 + W1 (a + 2) 0 := by unfold C1 W1; ring

/-- One unit at k = j + 3 without the level below. -/
def C2 (a j : ℕ) : ℕ := (2 * j + 7) * a + 4 * j + 15

theorem C2_eq (a j : ℕ) : C2 a j = (2 * (j + 1) + 5) * a + 4 * (j + 1) + 11 := by unfold C2; ring

/-- `T j n a`: the steps from B(j + 2, n, a) to B(j + 2, 0, g_j^n(a)). -/
def T : ℕ → ℕ → ℕ → ℕ
  | 0, n, a => ∑ i ∈ range n, C1 ((g 0)^[i] a)
  | j + 1, n, a => ∑ i ∈ range n, (C2 ((g (j + 1))^[i] a) j + T j ((g (j + 1))^[i] a + 2) 0)

theorem T_none (j a : ℕ) : T j 0 a = 0 := by
  cases j <;> simp [T]

theorem T_zero_succ (n a : ℕ) : T 0 (n + 1) a = C1 a + T 0 n (g 0 a) := by
  simp only [T]
  rw [sum_range_succ']
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  ring

theorem T_succ_succ (j n a : ℕ) :
    T (j + 1) (n + 1) a = C2 a j + T j (a + 2) 0 + T (j + 1) n (g (j + 1) a) := by
  simp only [T]
  rw [sum_range_succ']
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  ring

/-- The step count from the blank tape, the halting row included. -/
def tau : ℕ := 241 + T 14 3 0 + 1

/-- The number of nonblank cells on the halted tape. -/
def sigma : ℕ := (g 14)^[3] 0 + 18

/-- τ's body over a variable, at the definitional height of τ. -/
def tauF (t : ℕ) : ℕ := (fun _ : ℕ → ℕ → ℕ → ℕ => 241 + t + 1) T

/-- σ's body over a variable, at the definitional height of σ. -/
def sigF (a : ℕ) : ℕ := (fun _ : ℕ → ℕ → ℕ => a + 18) g

theorem tau_tauF : tau = tauF (T 14 3 0) := rfl

theorem tauF_eq (t : ℕ) : tauF t = 241 + t + 1 := rfl

theorem sigma_sigF : sigma = sigF ((g 14)^[3] 0) := rfl

theorem sigF_eq (a : ℕ) : sigF a = a + 18 := rfl

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.T_succ_succ
