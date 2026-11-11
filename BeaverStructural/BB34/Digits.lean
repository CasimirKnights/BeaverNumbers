import BeaverStructural.BB34.Numbers
import BeaverStructural.BB7.Digits

/-! The clock T_k(2↑↑h − 2, 0) of the BB(3,4) machine mod M = 10^200 at every level k, for h = 2, 4 and every tower
height h ≥ 206, on the tower residues of `BB7.Residues` and `BB7.ResiduesTall` (the g-hierarchy is the same).
Level 0 in closed form: 3·T_0(N, 0) + 72·2^N + 9N = 64·4^N + 8 (`T0_closed`), read mod M with the inverse of 3.
Level 1 is `L1` (its first 204 summands and one stable summand), level k + 1 ≥ 2 is `Lstep k` of the level-k triple.
`V k` is the triple (h = 2, 4, 206) at level k (`V_good`).  T_14(3, 0) is the summand at 0 and twice the summand at a
tall tower (`T14_mod`); τ mod M and σ mod M follow (`tau_mod`, `sigma_mod`). -/

namespace BeaverStructural.BB34

open Finset
open BeaverStructural.BB7 (g arrow arrow_two tow_mono tow_ge_of_four smallTow smallTow_eq md powMod powMod_eq cycle
  Tall g1_iter g2_tall gk_tall g0_iter M m1 inv3 three_inv3 M_big m1_big sumF sumF_eq sumF_split sumF_mod sub_mod'
  tw0 tw1 tw0_eq tw1_eq tw0_stable tw1_stable e1 e2 mulsub four_le_tow Nres N_mod Nres_stable pick pick_tall triple
  sumF_two sumF_one modeq_of_mod Ares g_add_four)

/-- 3·T_0(N, 0) + 72·2^N + 9N = 64·4^N + 8. -/
theorem T0_closed (N : ℕ) : 3 * T 0 N 0 + 72 * 2 ^ N + 9 * N = 64 * 4 ^ N + 8 := by
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
    generalize (g 0)^[N] 0 = a at hb ⊢
    generalize 2 ^ N = Y at hb ih ⊢
    zify at hb ih ⊢
    linear_combination ih + ((12 : ℤ) * a + 30 + 48 * Y) * hb

/-- The residue of T_0(N, 0) mod M from N mod M, 2^N mod M, 4^N mod M. -/
def T0res (Nm P2 P4 : ℕ) : ℕ := inv3 * (64 * P4 + 8 + 81 * M - (72 * P2 + 9 * Nm)) % M

theorem T0_mod (N : ℕ) : T 0 N 0 % M = T0res (N % M) (2 ^ N % M) (4 ^ N % M) := by
  have hMb := M_big
  have hMpos : 0 < M := by omega
  have hNm : N % M < M := Nat.mod_lt _ hMpos
  have hP2 : 2 ^ N % M < M := Nat.mod_lt _ hMpos
  set Nm := N % M
  set P2 := 2 ^ N % M
  set E := 64 * (4 ^ N % M) + 8 + 81 * M - (72 * P2 + 9 * Nm) with hE
  have hE' : E + (72 * P2 + 9 * Nm) = 64 * (4 ^ N % M) + 8 + 81 * M := by
    rw [hE]; omega
  have h3 : 3 * T 0 N 0 ≡ E [MOD M] := by
    apply Nat.ModEq.add_right_cancel' (72 * P2 + 9 * Nm)
    rw [hE']
    have hN : Nm ≡ N [MOD M] := Nat.mod_modEq N M
    have hP : P2 ≡ 2 ^ N [MOD M] := Nat.mod_modEq (2 ^ N) M
    calc 3 * T 0 N 0 + (72 * P2 + 9 * Nm) ≡ 3 * T 0 N 0 + (72 * 2 ^ N + 9 * N) [MOD M] :=
          Nat.ModEq.add_left _ ((hP.mul_left 72).add (hN.mul_left 9))
      _ = 64 * 4 ^ N + 8 := by rw [← T0_closed N]; ring
      _ ≡ 64 * (4 ^ N % M) + 8 [MOD M] := ((Nat.mod_modEq _ M).symm.mul_left 64).add_right 8
      _ ≡ 64 * (4 ^ N % M) + 8 + 81 * M [MOD M] := by
          show _ % M = _ % M; rw [Nat.add_mul_mod_self_right]
  have hinv : inv3 * 3 ≡ 1 [MOD M] := by
    show inv3 * 3 % M = 1 % M
    rw [mul_comm, three_inv3, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod]
  show T 0 N 0 % M = inv3 * E % M
  calc T 0 N 0 % M = 1 * T 0 N 0 % M := by rw [one_mul]
    _ = (inv3 * 3) * T 0 N 0 % M := hinv.symm.mul_right _
    _ = inv3 * (3 * T 0 N 0) % M := by rw [mul_assoc]
    _ = inv3 * E % M := Nat.ModEq.mul_left inv3 h3

theorem C1_mod (x m : ℕ) : C1 x % m = C1 (x % m) % m := by
  have h : x ≡ x % m [MOD m] := (Nat.mod_modEq x m).symm
  exact ((h.pow 2).mul_left 4).add (h.mul_left 26) |>.add_right 37

theorem C2_mod (x k m : ℕ) : C2 x k % m = C2 (x % m) k % m := by
  have h : x ≡ x % m [MOD m] := (Nat.mod_modEq x m).symm
  exact ((h.mul_left (2 * k + 7)).add_right (4 * k)).add_right 15

/-- The residue of T_0(2↑↑h − 2, 0) mod M. -/
def T0part (h : ℕ) : ℕ := T0res ((tw0 h + M - 2) % M) (powMod 2 (e1 h) M) (powMod 2 (e2 h) M)

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

/-- The level-(k + 1) summand: C2(b_i, k) + T_k(b_i + 2, 0), b_i = g_(k+1)^i(0). -/
def fk (k i : ℕ) : ℕ := C2 ((g (k + 1))^[i] 0) k + T k ((g (k + 1))^[i] 0 + 2) 0

theorem T_succ_zero (k N : ℕ) : T (k + 1) N 0 = sumF (fk k) N := by
  rw [sumF_eq]; rfl

theorem T_one_zero (N : ℕ) : T 1 N 0 = sumF (fk 0) N := T_succ_zero 0 N

theorem T_zero_of (k j N : ℕ) (h : j + 1 = k) : T k N 0 = sumF (fk j) N := by
  subst h; exact T_succ_zero j N

theorem sumF_three (f : ℕ → ℕ) : sumF f 3 = 0 + f 0 + f 1 + f 2 := rfl

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

/-- T_1(N, 0) mod M as its N summands. -/
theorem T1_small (N : ℕ) : T 1 N 0 % M = sumF term1 N % M := by
  rw [T_one_zero]
  exact sumF_mod (fk 0) term1 M (fun i => by rw [term1_eq, term1_mod]) N

/-- T_1(2↑↑h − 2, 0) mod M. -/
def L1 (h : ℕ) : ℕ :=
  if h ≤ 3 then sumF term1 (smallTow h - 2) % M
  else (sumF term1 204 % M + (Nres h + M - 204) % M * term1 204) % M

theorem L1_eq (h : ℕ) (hh : 2 ≤ h) : T 1 (arrow 2 h - 2) 0 % M = L1 h := by
  unfold L1
  by_cases hs : h ≤ 3
  · rw [if_pos hs, T1_small, smallTow_eq h (by omega)]
  · rw [if_neg hs]
    have hbig : 65536 ≤ arrow 2 h := tow_ge_of_four (by omega)
    rw [T1_split _ (by omega), Nat.add_mod, mulsub _ _ _ (by omega) (by have := M_big; omega), N_mod h hh,
      Nat.add_mod_mod]

theorem L1_stable {z : ℕ} (hz : 206 ≤ z) : L1 z = L1 206 := by
  unfold L1; rw [if_neg (by omega), if_neg (by norm_num), Nres_stable hz]

/-- p holds the residues of T_k(2↑↑h − 2, 0) mod M at h = 2, 4 and every tall h. -/
def Good (k : ℕ) (p : ℕ × ℕ × ℕ) : Prop :=
  ∀ h, (h = 2 ∨ h = 4 ∨ 206 ≤ h) → T k (arrow 2 h - 2) 0 % M = pick p h

/-- The level-(k + 1) summand residue at b + 4 = 2↑↑ht with T_k(b + 2, 0) ≡ v. -/
def u (k ht v : ℕ) : ℕ := (C2 ((tw0 ht + M - 4) % M) k + v) % M

theorem fk_mod (k : ℕ) (p : ℕ × ℕ × ℕ) (hp : Good k p) (i ht : ℕ) (hb : (g (k + 1))^[i] 0 + 4 = arrow 2 ht)
    (hht : ht = 2 ∨ ht = 4 ∨ 206 ≤ ht) : fk k i % M = u k ht (pick p ht) := by
  have h2 : 2 ≤ ht := by omega
  have h4 := four_le_tow h2
  have eb : (g (k + 1))^[i] 0 = arrow 2 ht - 4 := by omega
  have eN : (g (k + 1))^[i] 0 + 2 = arrow 2 ht - 2 := by omega
  have hbM : ((g (k + 1))^[i] 0) % M = (tw0 ht + M - 4) % M := by
    rw [eb, sub_mod' _ _ _ h4 (by have := M_big; omega), tw0_eq]
  unfold fk u
  rw [Nat.add_mod, C2_mod, hbM, eN, hp ht hht, Nat.mod_add_mod]

theorem u_stable {k z v : ℕ} (hz : 206 ≤ z) : u k z v = u k 206 v := by unfold u; rw [tw0_stable hz]

/-- T_(k+1)(2↑↑h − 2, 0) mod M from the level-k triple. -/
def Lstep (k : ℕ) (p : ℕ × ℕ × ℕ) (h : ℕ) : ℕ :=
  if k = 1 then (u 1 2 p.1 + u 1 4 p.2.1 + (Nres h + M - 2) % M * u 1 206 p.2.2) % M
  else (u k 2 p.1 + (Nres h + M - 1) % M * u k 206 p.2.2) % M

theorem Lstep_stable (k : ℕ) (p : ℕ × ℕ × ℕ) {z : ℕ} (hz : 206 ≤ z) : Lstep k p z = Lstep k p 206 := by
  unfold Lstep; rw [Nres_stable hz]

theorem level_succ (k : ℕ) (hk : 1 ≤ k) (p : ℕ × ℕ × ℕ) (hp : Good k p) (h : ℕ) (hh : 2 ≤ h) :
    T (k + 1) (arrow 2 h - 2) 0 % M = Lstep k p h := by
  have h4 := four_le_tow hh
  have hMb := M_big
  rw [T_succ_zero]
  have b0 : (g (k + 1))^[0] 0 + 4 = arrow 2 2 := by rw [arrow_two]; rfl
  have f0 := fk_mod k p hp 0 2 b0 (Or.inl rfl)
  by_cases k1 : k = 1
  · subst k1
    have b1 : (g 2)^[1] 0 + 4 = arrow 2 4 := by rw [Function.iterate_one, g_add_four]
    have f1 := fk_mod 1 p hp 1 4 b1 (Or.inr (Or.inl rfl))
    have tail : ∀ i, 2 ≤ i → fk 1 i % M = u 1 206 (pick p 206) := by
      intro i hi
      obtain ⟨z, hz, e⟩ := g2_tall (i - 2)
      rw [show i - 2 + 2 = i by omega] at e
      rw [fk_mod 1 p hp i z e (Or.inr (Or.inr hz)), u_stable hz, pick_tall p hz, pick_tall p le_rfl]
    rw [sumF_split (fk 1) M 2 _ _ (by omega) tail, sumF_two]
    unfold Lstep
    rw [if_pos rfl]
    have c := ((modeq_of_mod f0).add (modeq_of_mod f1)).add
      (modeq_of_mod (mulsub (arrow 2 h - 2) 2 (u 1 206 (pick p 206)) (by omega) (by omega)))
    rw [N_mod h hh] at c
    have e2 : pick p 2 = p.1 := by simp [pick]
    have e4 : pick p 4 = p.2.1 := by simp [pick]
    rw [e2, e4, pick_tall p le_rfl] at c
    rw [pick_tall p le_rfl]
    exact c.trans ((Nat.ModEq.refl _).add (Nat.mod_modEq _ M))
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have tail : ∀ i, 1 ≤ i → fk (j + 2) i % M = u (j + 2) 206 (pick p 206) := by
      intro i hi
      obtain ⟨z, hz, e⟩ := gk_tall j (i - 1)
      rw [show i - 1 + 1 = i by omega, show j + 3 = j + 2 + 1 by ring] at e
      rw [fk_mod (j + 2) p hp i z e (Or.inr (Or.inr hz)), u_stable hz, pick_tall p hz, pick_tall p le_rfl]
    rw [sumF_split (fk (j + 2)) M 1 _ _ (by omega) tail, sumF_one]
    unfold Lstep
    rw [if_neg (by omega)]
    have c := (modeq_of_mod f0).add
      (modeq_of_mod (mulsub (arrow 2 h - 2) 1 (u (j + 2) 206 (pick p 206)) (by omega) (by omega)))
    rw [N_mod h hh] at c
    have e2 : pick p 2 = p.1 := by simp [pick]
    rw [e2, pick_tall p le_rfl] at c
    rw [pick_tall p le_rfl]
    exact c.trans ((Nat.ModEq.refl _).add (Nat.mod_modEq _ M))

theorem good_triple (k : ℕ) (f : ℕ → ℕ) (H : ∀ h, 2 ≤ h → T k (arrow 2 h - 2) 0 % M = f h)
    (S : ∀ z, 206 ≤ z → f z = f 206) : Good k (triple f) := by
  intro h hh
  rcases hh with rfl | rfl | hz
  · rw [H 2 le_rfl]; rfl
  · rw [H 4 (by norm_num)]; rfl
  · rw [H h (by omega), S h hz, pick_tall _ hz]; rfl

/-- The level table: V k = residues of T_k(2↑↑h − 2, 0) mod M at h = 2, 4, 206. -/
def V : ℕ → ℕ × ℕ × ℕ
  | 0 => triple T0part
  | 1 => triple L1
  | k + 2 => triple (Lstep (k + 1) (V (k + 1)))

theorem V_good : ∀ k, Good k (V k)
  | 0 => good_triple 0 T0part (fun h hh => T0part_eq h hh) (fun _ hz => T0part_stable hz)
  | 1 => good_triple 1 L1 (fun h hh => L1_eq h hh) (fun _ hz => L1_stable hz)
  | k + 2 => good_triple (k + 2) (Lstep (k + 1) (V (k + 1)))
      (fun h hh => level_succ (k + 1) (by omega) _ (V_good (k + 1)) h hh) (fun _ hz => Lstep_stable _ _ hz)

theorem V_step (j k : ℕ) (h : k + 1 = j) : V (k + 2) = triple (Lstep j (V j)) := by subst h; rfl

/-- T_14(3, 0) mod M: the summand at 0 and twice the summand at a tall tower. -/
theorem T14_mod : T 14 3 0 ≡ 0 + u 13 2 (V 13).1 + u 13 206 (V 13).2.2 + u 13 206 (V 13).2.2 [MOD M] := by
  have hp := V_good 13
  have b0 : (g (13 + 1))^[0] 0 + 4 = arrow 2 2 := by rw [arrow_two]; rfl
  have f0 := fk_mod 13 (V 13) hp 0 2 b0 (Or.inl rfl)
  have tail : ∀ i, 1 ≤ i → fk 13 i % M = u 13 206 (pick (V 13) 206) := by
    intro i hi
    obtain ⟨z, hz, e⟩ := gk_tall 11 (i - 1)
    rw [show i - 1 + 1 = i by omega] at e
    rw [fk_mod 13 (V 13) hp i z e (Or.inr (Or.inr hz)), u_stable hz, pick_tall _ hz, pick_tall _ le_rfl]
  have e2 : pick (V 13) 2 = (V 13).1 := by simp [pick]
  have c := (((Nat.ModEq.refl 0).add (modeq_of_mod f0)).add (modeq_of_mod (tail 1 le_rfl))).add
    (modeq_of_mod (tail 2 (by norm_num)))
  rw [e2, pick_tall (V 13) le_rfl] at c
  rw [T_zero_of 14 13 3 rfl, sumF_three]
  exact c

/-- τ mod M from the level table. -/
theorem tau_mod : tau ≡ 241 + (0 + u 13 2 (V 13).1 + u 13 206 (V 13).2.2 + u 13 206 (V 13).2.2) + 1 [MOD M] := by
  rw [tau_tauF, tauF_eq]
  exact ((Nat.ModEq.refl 241).add T14_mod).add_right 1

/-- g_(j+3)^(i+1)(0) mod M is the tall residue less 4. -/
theorem iter_tall_mod (j i : ℕ) : (g (j + 3))^[i + 1] 0 % M = Ares := by
  obtain ⟨z, hz, e⟩ := gk_tall j i
  have h4 := four_le_tow (show 2 ≤ z by omega)
  have e' : (g (j + 3))^[i + 1] 0 = arrow 2 z - 4 := by omega
  rw [e', sub_mod' _ _ _ h4 (by have := M_big; omega), ← tw0_eq, tw0_stable hz]
  rfl

theorem iter_tall_mod' (k n : ℕ) (hk : 3 ≤ k) (hn : 1 ≤ n) : (g k)^[n] 0 % M = Ares := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  exact iter_tall_mod j i

/-- σ = g_14^3(0) + 18 ≡ Ares + 18 (mod M). -/
theorem sigma_mod : sigma ≡ Ares + 18 [MOD M] := by
  have hA : (g 14)^[3] 0 % M = Ares := iter_tall_mod' 14 3 (by norm_num) (by norm_num)
  rw [sigma_sigF, sigF_eq]
  exact (modeq_of_mod hA).add_right 18

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.T0_mod
#print axioms BeaverStructural.BB34.L1_eq
#print axioms BeaverStructural.BB34.level_succ
#print axioms BeaverStructural.BB34.V_good
#print axioms BeaverStructural.BB34.tau_mod
#print axioms BeaverStructural.BB34.sigma_mod
