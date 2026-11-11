import BeaverStructural.BB7.Residues
import Mathlib.Tactic.LinearCombination

/-! Tall towers and the level-0 and level-1 clocks of the BB(7) champion mod M = 10^200.
`Tall x`: x = 2↑↑z with z ≥ 206.  Tall is preserved by 2↑^k (k ≥ 1) and by g_k (k ≥ 1) on b + 4; the iterates of
g_k from 0 are Tall on b + 4 from index 2 (k = 2) and 1 (k ≥ 3); a sequence a with a 2 = 65532 and
a (j + 1) = g_j(a j) is Tall on a (j + 3) + 4.  T_0 closed form: 3·T_0(N, 0) + 936 + 318N = 576·4^N + 360·2^N,
read mod M with the inverse of 3.  `sumF_split`: a sum whose terms have one residue from i0 on is its prefix plus
(N − i0) copies.  The level-1 summand at index i is `term1 i` mod M, constant from i = 204. -/

namespace BeaverStructural.BB7

open Finset

/-- x is a tower 2↑↑z of height z ≥ 206. -/
def Tall (x : ℕ) : Prop := ∃ z, 206 ≤ z ∧ x = arrow 2 z

theorem arrow_tower (j : ℕ) : ∀ y, 1 ≤ y → ∃ z, y ≤ z ∧ arrow (j + 2) y = arrow 2 z := by
  induction j with
  | zero => intro y _; exact ⟨y, le_rfl, rfl⟩
  | succ j ih =>
    intro y hy
    induction y, hy using Nat.le_induction with
    | base => exact ⟨1, le_rfl, by rw [arrow_one, arrow_one]⟩
    | succ y hy _ =>
      rw [show j + 1 + 2 = (j + 2) + 1 by ring, arrow_succ_succ]
      have hw := arrow_gt (j + 2) y
      obtain ⟨z, hz, e⟩ := ih (arrow (j + 2 + 1) y) (by omega)
      exact ⟨z, by omega, e⟩

theorem tall_arrow (k : ℕ) (hk : 1 ≤ k) {x : ℕ} (hx : Tall x) : Tall (arrow k x) := by
  obtain ⟨z, hz, rfl⟩ := hx
  by_cases h1 : k = 1
  · subst h1; exact ⟨z + 1, by omega, by rw [arrow_one_eq, tow_succ]⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hgt : z < arrow 2 z := arrow_gt 1 z
    obtain ⟨z', hz', e⟩ := arrow_tower j (arrow 2 z) (by omega)
    exact ⟨z', by omega, e⟩

theorem g_add_four (k b : ℕ) : g k b + 4 = arrow k (b + 4) := by
  rw [g_eq_arrow, Nat.sub_add_cancel (arrow_ge _ _ (by omega))]

theorem g_tall (k : ℕ) (hk : 1 ≤ k) {b : ℕ} (hb : Tall (b + 4)) : Tall (g k b + 4) := by
  rw [g_add_four]; exact tall_arrow k hk hb

theorem iter_tall (k : ℕ) (hk : 1 ≤ k) (b : ℕ) (hb : Tall (b + 4)) : ∀ i, Tall ((g k)^[i] b + 4) := by
  intro i
  induction i with
  | zero => exact hb
  | succ i ih => rw [Function.iterate_succ_apply']; exact g_tall k hk ih

theorem iter_two (f : ℕ → ℕ) (x : ℕ) : f^[2] x = f (f x) := rfl

theorem g1_iter (i : ℕ) : (g 1)^[i] 0 + 4 = arrow 2 (i + 2) := by
  induction i with
  | zero => simp [arrow_two]
  | succ i ih =>
    rw [Function.iterate_succ_apply', g_add_four, ih, arrow_one_eq, show i + 1 + 2 = (i + 2) + 1 by ring]
    exact (tow_succ (i + 2)).symm

theorem g2_base : Tall ((g 2)^[2] 0 + 4) := by
  rw [iter_two, g_add_four, g_add_four]
  exact ⟨arrow 2 (0 + 4), by decide +kernel, rfl⟩

theorem g2_tall (i : ℕ) : Tall ((g 2)^[i + 2] 0 + 4) := by
  rw [Function.iterate_add_apply]
  exact iter_tall 2 (by norm_num) _ g2_base i

theorem arrow_four_tall (j : ℕ) : Tall (arrow (j + 3) 4) := by
  have e3 : arrow (j + 3) 3 = arrow (j + 2) 4 := by
    rw [show (3 : ℕ) = 2 + 1 by rfl, show j + 3 = (j + 2) + 1 by ring, arrow_succ_succ, arrow_two]
  have e4 : arrow (j + 3) 4 = arrow (j + 2) (arrow (j + 2) 4) := by
    rw [show (4 : ℕ) = 3 + 1 by rfl, show j + 3 = (j + 2) + 1 by ring, arrow_succ_succ]
    rw [show j + 2 + 1 = j + 3 by ring, e3]
  obtain ⟨z, hz, e⟩ := arrow_tower j 4 (by norm_num)
  have hy : 206 ≤ arrow (j + 2) 4 := by rw [e]; have := tow_ge_of_four hz; omega
  obtain ⟨z', hz', e'⟩ := arrow_tower j (arrow (j + 2) 4) (by omega)
  exact ⟨z', by omega, by rw [e4, e']⟩

theorem gk_tall (j i : ℕ) : Tall ((g (j + 3))^[i + 1] 0 + 4) := by
  rw [Function.iterate_add_apply, Function.iterate_one]
  refine iter_tall (j + 3) (by omega) _ ?_ i
  rw [g_add_four]; exact arrow_four_tall j

/-- A sequence with a 2 = 65532 and a (j + 1) = g_j(a j) is Tall on a (j + 3) + 4. -/
theorem seq_tall (a : ℕ → ℕ) (h2 : a 2 = 65532) (hs : ∀ j, a (j + 1) = g j (a j)) (j : ℕ) :
    Tall (a (j + 3) + 4) := by
  induction j with
  | zero =>
    rw [hs 2, h2, g_add_four]
    exact ⟨65532 + 4, by norm_num, rfl⟩
  | succ j ih =>
    rw [show j + 1 + 3 = (j + 3) + 1 by ring, hs (j + 3)]
    exact g_tall (j + 3) (by omega) ih

theorem tall_ge {x : ℕ} (hx : Tall x) : 65536 ≤ x := by
  obtain ⟨z, hz, rfl⟩ := hx; exact tow_ge_of_four (by omega)

theorem g0_iter (i : ℕ) : (g 0)^[i] 0 + 4 = 4 * 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    show 2 * ((g 0)^[i] 0) + 4 + 4 = 4 * 2 ^ (i + 1)
    rw [pow_succ]; omega

/-- 3·T_0(N, 0) + 936 + 318N = 576·4^N + 360·2^N. -/
theorem T0_closed (N : ℕ) : 3 * T 0 N 0 + 936 + 318 * N = 576 * 4 ^ N + 360 * 2 ^ N := by
  induction N with
  | zero => simp [T]
  | succ N ih =>
    have hs : T 0 (N + 1) 0 = T 0 N 0 + C1 ((g 0)^[N] 0) := by
      simp only [T]; rw [Finset.sum_range_succ]
    have hb := g0_iter N
    have h4 : (4 : ℕ) ^ N = (2 ^ N) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [hs, pow_succ, pow_succ, h4]
    rw [h4] at ih
    unfold C1
    generalize (g 0)^[N] 0 = a at hb
    generalize 2 ^ N = Y at hb ih ⊢
    zify at hb ih ⊢
    linear_combination ih + ((108 : ℤ) * (a + 4 + 4 * Y) + 90) * hb

/-- M = 10^200 = 2^200·5^200 and its first exponent modulus m1 = 4·5^199. -/
def M : ℕ := md 200 200
def m1 : ℕ := md 2 199
def inv3 : ℕ := (2 * M + 1) / 3

theorem three_inv3 : 3 * inv3 = 2 * M + 1 := by
  unfold inv3; decide +kernel

theorem M_eq : M = 10 ^ 200 := by decide +kernel

/-- The residue of T_0(N, 0) mod M from N mod M, 2^N mod M, 4^N mod M. -/
def T0res (Nm P2 P4 : ℕ) : ℕ := inv3 * (576 * P4 + 360 * P2 + 319 * M - (936 + 318 * Nm)) % M

theorem M_big : 1000 ≤ M := by unfold M md; norm_num

theorem T0_mod (N : ℕ) : T 0 N 0 % M = T0res (N % M) (2 ^ N % M) (4 ^ N % M) := by
  have hMpos : 0 < M := by have := M_big; omega
  have hNm : N % M < M := Nat.mod_lt _ hMpos
  set Nm := N % M
  set E := 576 * (4 ^ N % M) + 360 * (2 ^ N % M) + 319 * M - (936 + 318 * Nm) with hE
  have hle : 936 + 318 * Nm ≤ 576 * (4 ^ N % M) + 360 * (2 ^ N % M) + 319 * M := by
    have := M_big; omega
  have hE' : E + (936 + 318 * Nm) = 576 * (4 ^ N % M) + 360 * (2 ^ N % M) + 319 * M := by
    rw [hE]; omega
  have h3 : 3 * T 0 N 0 ≡ E [MOD M] := by
    apply Nat.ModEq.add_right_cancel' (936 + 318 * Nm)
    rw [hE']
    have hN : N ≡ Nm [MOD M] := (Nat.mod_modEq N M).symm
    calc 3 * T 0 N 0 + (936 + 318 * Nm) ≡ 3 * T 0 N 0 + (936 + 318 * N) [MOD M] :=
          Nat.ModEq.add_left _ ((hN.symm.mul_left 318).add_left 936)
      _ = 576 * 4 ^ N + 360 * 2 ^ N := by rw [← T0_closed N]; ring
      _ ≡ 576 * (4 ^ N % M) + 360 * (2 ^ N % M) [MOD M] :=
          (((Nat.mod_modEq _ M).symm.mul_left 576).add ((Nat.mod_modEq _ M).symm.mul_left 360))
      _ ≡ 576 * (4 ^ N % M) + 360 * (2 ^ N % M) + 319 * M [MOD M] := by
          show _ % M = _ % M; rw [Nat.add_mul_mod_self_right]
  have hinv : inv3 * 3 ≡ 1 [MOD M] := by
    show inv3 * 3 % M = 1 % M
    rw [mul_comm, three_inv3, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
  show T 0 N 0 % M = inv3 * E % M
  calc T 0 N 0 % M = 1 * T 0 N 0 % M := by rw [one_mul]
    _ = (inv3 * 3) * T 0 N 0 % M := hinv.symm.mul_right _
    _ = inv3 * (3 * T 0 N 0) % M := by rw [mul_assoc]
    _ = inv3 * E % M := Nat.ModEq.mul_left inv3 h3

/-- A sum over 0 ≤ i < n. -/
def sumF (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumF f n + f n

theorem sumF_eq (f : ℕ → ℕ) (n : ℕ) : sumF f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumF, ih, Finset.sum_range_succ]

/-- A sum whose terms have one residue from i0 on is its prefix plus (N − i0) copies. -/
theorem sumF_split (f : ℕ → ℕ) (m i0 N s : ℕ) (hN : i0 ≤ N) (hs : ∀ i, i0 ≤ i → f i % m = s) :
    sumF f N % m = (sumF f i0 + (N - i0) * s) % m := by
  induction N, hN using Nat.le_induction with
  | base => rw [Nat.sub_self, zero_mul, add_zero]
  | succ N hN ih =>
    rw [sumF, show N + 1 - i0 = (N - i0) + 1 by omega, add_mul, one_mul]
    have hf : f N ≡ s [MOD m] := by
      have e := hs N hN
      show f N % m = s % m
      rw [← e, Nat.mod_mod]
    have : sumF f N + f N ≡ sumF f i0 + (N - i0) * s + s [MOD m] := Nat.ModEq.add ih hf
    rw [← add_assoc]; exact this

theorem sumF_mod (f h : ℕ → ℕ) (m : ℕ) (hf : ∀ i, f i % m = h i % m) : ∀ n, sumF f n % m = sumF h n % m := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact Nat.ModEq.add ih (hf n)

theorem sub_mod' (x c m : ℕ) (hc : c ≤ x) (hcm : c ≤ m) : (x - c) % m = (x % m + m - c) % m := by
  apply Nat.ModEq.add_right_cancel' c
  rw [Nat.sub_add_cancel hc, Nat.sub_add_cancel (by omega)]
  show x % m = (x % m + m) % m
  rw [Nat.add_mod_right, Nat.mod_mod]

theorem C1_mod (x m : ℕ) : C1 x % m = C1 (x % m) % m := by
  have h : x ≡ x % m [MOD m] := (Nat.mod_modEq x m).symm
  exact ((h.pow 2).mul_left 36).add (h.mul_left 318) |>.add_right 590

theorem C2_mod (x k m : ℕ) : C2 x k % m = C2 (x % m) k % m := by
  have h : x ≡ x % m [MOD m] := (Nat.mod_modEq x m).symm
  exact ((((h.mul_left 3).add_right 1).mul_left (24 + 8 * k)).add_right 226).add_right (48 * k)

theorem CH_mod (x k m : ℕ) : CH x k % m = CH (x % m) k % m := by
  have h : x ≡ x % m [MOD m] := (Nat.mod_modEq x m).symm
  exact ((((h.mul_left 3).add_right 1).mul_left (2 + 8 * k)).add_right 27).add_right (21 * k)

/-- Tower residues at the two moduli read by the T_0 closed form. -/
def tw0 (h : ℕ) : ℕ := towMod h 200 200
def tw1 (h : ℕ) : ℕ := towMod h 2 199

theorem tw0_eq (h : ℕ) : tw0 h = arrow 2 h % M := towMod_eq h 200 200 (by norm_num)
theorem tw1_eq (h : ℕ) : tw1 h = arrow 2 h % m1 := towMod_eq h 2 199 (by norm_num)

theorem tw0_stable {z : ℕ} (hz : 206 ≤ z) : tw0 z = tw0 206 := by
  rw [tw0_eq, tw0_eq, M, stable 200 200 z (by norm_num) hz]

theorem tw1_stable {z : ℕ} (hz : 206 ≤ z) : tw1 z = tw1 206 := by
  rw [tw1_eq, tw1_eq, m1, stable 199 2 z (by norm_num) (by omega), stable 199 2 206 (by norm_num) (by omega)]

/-- Exponents reading 2^N and 4^N for N = 2↑↑h − 2. -/
def e1 (h : ℕ) : ℕ := if h ≤ 3 then smallTow h - 2 else (tw1 h + m1 - 2) % m1 + m1 * 200
def e2 (h : ℕ) : ℕ := if h ≤ 3 then 2 * (smallTow h - 2) else 2 * ((tw1 h + m1 - 2) % m1) % m1 + m1 * 200

/-- The residue of T_0(2↑↑h − 2, 0) mod M. -/
def T0part (h : ℕ) : ℕ := T0res ((tw0 h + M - 2) % M) (powMod 2 (e1 h) M) (powMod 2 (e2 h) M)

theorem m1_big : 1000 ≤ m1 := by unfold m1 md; norm_num

theorem T0part_eq (h : ℕ) (hh : 2 ≤ h) : T 0 (arrow 2 h - 2) 0 % M = T0part h := by
  have h4 : 4 ≤ arrow 2 h := by rw [← arrow_two 2]; exact tow_mono hh
  rw [T0_mod]
  unfold T0part
  have hN : (arrow 2 h - 2) % M = (tw0 h + M - 2) % M := by
    rw [sub_mod' _ _ _ (by omega) (by have := M_big; omega), tw0_eq]
  have h4N : (4 : ℕ) ^ (arrow 2 h - 2) = 2 ^ (2 * (arrow 2 h - 2)) := by rw [pow_mul]; norm_num
  by_cases hs : h ≤ 3
  · have hsm : smallTow h = arrow 2 h := smallTow_eq h (by omega)
    simp only [e1, e2, hs, if_true, hsm, powMod_eq, hN, h4N]
  · have hbig : 65536 ≤ arrow 2 h := tow_ge_of_four (by omega)
    have hN1 : (arrow 2 h - 2) % m1 = (tw1 h + m1 - 2) % m1 := by
      rw [sub_mod' _ _ _ (by omega) (by have := m1_big; omega), tw1_eq]
    have c1 := cycle 200 199 (arrow 2 h - 2) (by omega)
    have c2 := cycle 200 199 (2 * (arrow 2 h - 2)) (by omega)
    rw [Nat.mul_mod, show 2 % md 2 199 = 2 by unfold md; norm_num] at c2
    simp only [e1, e2, hs, if_false, powMod_eq, hN, h4N]
    rw [show md 200 200 = M from rfl, show md 2 199 = m1 from rfl] at c1 c2
    rw [c1, c2, hN1]

theorem T0part_stable {z : ℕ} (hz : 206 ≤ z) : T0part z = T0part 206 := by
  unfold T0part e1 e2
  rw [tw0_stable hz, tw1_stable hz]
  simp only [show ¬ z ≤ 3 by omega, show ¬ (206 : ℕ) ≤ 3 by norm_num, if_false]

theorem T0_tall (N : ℕ) (hN : Tall (N + 2)) : T 0 N 0 % M = T0part 206 := by
  obtain ⟨z, hz, e⟩ := hN
  rw [show N = arrow 2 z - 2 by omega, T0part_eq z (by omega), T0part_stable hz]

theorem tall_mod {x : ℕ} (hx : Tall x) : x % M = tw0 206 := by
  obtain ⟨z, hz, rfl⟩ := hx; rw [← tw0_eq, tw0_stable hz]

/-- The level-(k + 1) summand: C2(b_i, k) + T_k(b_i + 2, 0), b_i = g_(k+1)^i(0). -/
def fk (k i : ℕ) : ℕ := C2 ((g (k + 1))^[i] 0) k + T k ((g (k + 1))^[i] 0 + 2) 0

theorem T_succ_zero (k N : ℕ) : T (k + 1) N 0 = sumF (fk k) N := by
  rw [sumF_eq]; rfl

theorem T_one_zero (N : ℕ) : T 1 N 0 = sumF (fk 0) N := T_succ_zero 0 N

theorem T_succ_one (k a : ℕ) : T (k + 1) 1 a = C2 a k + T k (a + 2) 0 := by
  show ∑ i ∈ range 1, (C2 ((g (k + 1))^[i] a) k + T k ((g (k + 1))^[i] a + 2) 0) = _
  rw [Finset.sum_range_one]; rfl

theorem T_zero_one (a : ℕ) : T 0 1 a = C1 a := by
  show ∑ i ∈ range 1, C1 ((g 0)^[i] a) = _
  rw [Finset.sum_range_one]; rfl

/-- The residue of the level-1 summand at index i. -/
def term1 (i : ℕ) : ℕ := (C2 ((tw0 (i + 2) + M - 4) % M) 0 + T0part (i + 2)) % M

theorem term1_eq (i : ℕ) : fk 0 i % M = term1 i := by
  show (C2 ((g 1)^[i] 0) 0 + T 0 ((g 1)^[i] 0 + 2) 0) % M = term1 i
  have hb := g1_iter i
  have h4 : 4 ≤ arrow 2 (i + 2) := by rw [← arrow_two 2]; exact tow_mono (by omega)
  have eb : (g 1)^[i] 0 = arrow 2 (i + 2) - 4 := by omega
  have eN : (g 1)^[i] 0 + 2 = arrow 2 (i + 2) - 2 := by omega
  unfold term1
  rw [Nat.add_mod, C2_mod, eN, T0part_eq (i + 2) (by omega), eb,
    sub_mod' _ _ _ h4 (by have := M_big; omega), tw0_eq, Nat.mod_add_mod]

theorem term1_stable {i : ℕ} (hi : 204 ≤ i) : term1 i = term1 204 := by
  unfold term1
  rw [tw0_stable (show 206 ≤ i + 2 by omega), T0part_stable (show 206 ≤ i + 2 by omega)]

theorem term1_mod (i : ℕ) : term1 i % M = term1 i := by unfold term1; rw [Nat.mod_mod]

/-- T_1(N, 0) mod M for N ≥ 204: the first 204 summands plus (N − 204) stable summands. -/
theorem T1_split (N : ℕ) (hN : 204 ≤ N) : T 1 N 0 % M = (sumF term1 204 + (N - 204) * term1 204) % M := by
  rw [T_one_zero, sumF_split (fk 0) M 204 N (term1 204) hN (fun i hi => by rw [term1_eq, term1_stable hi])]
  have hp : sumF (fk 0) 204 % M = sumF term1 204 % M :=
    sumF_mod (fk 0) term1 M (fun i => by rw [term1_eq, term1_mod]) 204
  exact Nat.ModEq.add_right _ hp

/-- T_1(N, 0) mod M for N < 204 as its N summands. -/
theorem T1_small (N : ℕ) : T 1 N 0 % M = sumF term1 N % M := by
  rw [T_one_zero]
  exact sumF_mod (fk 0) term1 M (fun i => by rw [term1_eq, term1_mod]) N

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.seq_tall
#print axioms BeaverStructural.BB7.gk_tall
#print axioms BeaverStructural.BB7.g2_tall
#print axioms BeaverStructural.BB7.T0_mod
#print axioms BeaverStructural.BB7.T0_tall
#print axioms BeaverStructural.BB7.T1_split
#print axioms BeaverStructural.BB7.T1_small
#print axioms BeaverStructural.BB7.T_succ_one
#print axioms BeaverStructural.BB7.M_eq
