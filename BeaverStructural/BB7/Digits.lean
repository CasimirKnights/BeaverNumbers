import BeaverStructural.BB7.ResiduesTall
/-! The clock T_k(2↑↑h − 2, 0) mod M = 10^200 at every level k, for h = 2, 4 and every tower height h ≥ 206.
Level 0 is `T0part`, level 1 is `L1` (its first 204 summands and one stable summand), level k + 1 ≥ 2 is
`Lstep k` of the level-k triple: from index 2 (k = 1) or 1 (k ≥ 2) on, b_i + 4 is a tall tower and the summand
C2(b_i, k) + T_k(b_i + 2, 0) has one residue.  `V k` is the triple (h = 2, 4, 206) at level k (`V_good`).
τ mod M and σ mod M are read from the triples (`tau_mod`, `sigma_mod`). -/

namespace BeaverStructural.BB7

open Finset

theorem mulsub (N i0 s : ℕ) (hN : i0 ≤ N) (hi : i0 ≤ M) :
    (N - i0) * s % M = ((N % M + M - i0) % M * s) % M := by
  rw [Nat.mul_mod, sub_mod' N i0 M hN hi]
  conv_rhs => rw [Nat.mul_mod, Nat.mod_mod]

theorem four_le_tow {h : ℕ} (hh : 2 ≤ h) : 4 ≤ arrow 2 h := by
  rw [← arrow_two 2]; exact tow_mono hh

/-- (2↑↑h − 2) mod M. -/
def Nres (h : ℕ) : ℕ := (tw0 h + M - 2) % M

theorem N_mod (h : ℕ) (hh : 2 ≤ h) : (arrow 2 h - 2) % M = Nres h := by
  have := four_le_tow hh
  rw [sub_mod' _ _ _ (by omega) (by have := M_big; omega), ← tw0_eq]; rfl

theorem Nres_stable {z : ℕ} (hz : 206 ≤ z) : Nres z = Nres 206 := by unfold Nres; rw [tw0_stable hz]

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

/-- The value of a triple at h: h = 2, h = 4, else the tall value. -/
def pick (p : ℕ × ℕ × ℕ) (h : ℕ) : ℕ := if h = 2 then p.1 else if h = 4 then p.2.1 else p.2.2

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

theorem pick_tall (p : ℕ × ℕ × ℕ) {z : ℕ} (hz : 206 ≤ z) : pick p z = p.2.2 := by
  unfold pick; rw [if_neg (by omega), if_neg (by omega)]

/-- T_(k+1)(2↑↑h − 2, 0) mod M from the level-k triple. -/
def Lstep (k : ℕ) (p : ℕ × ℕ × ℕ) (h : ℕ) : ℕ :=
  if k = 1 then (u 1 2 p.1 + u 1 4 p.2.1 + (Nres h + M - 2) % M * u 1 206 p.2.2) % M
  else (u k 2 p.1 + (Nres h + M - 1) % M * u k 206 p.2.2) % M

theorem Lstep_stable (k : ℕ) (p : ℕ × ℕ × ℕ) {z : ℕ} (hz : 206 ≤ z) : Lstep k p z = Lstep k p 206 := by
  unfold Lstep; rw [Nres_stable hz]

theorem sumF_two (f : ℕ → ℕ) : sumF f 2 = f 0 + f 1 := by simp [sumF]
theorem sumF_one (f : ℕ → ℕ) : sumF f 1 = f 0 := by simp [sumF]

theorem modeq_of_mod {a b : ℕ} (h : a % M = b) : a ≡ b [MOD M] := by
  show a % M = b % M
  rw [h]
  have : b < M := by rw [← h]; exact Nat.mod_lt _ (by have := M_big; omega)
  exact (Nat.mod_eq_of_lt this).symm

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

/-- The values of f at h = 2, 4, 206. -/
def triple (f : ℕ → ℕ) : ℕ × ℕ × ℕ := (f 2, f 4, f 206)

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

/-- A_j mod M for j ≥ 3 (A_j + 4 is a tall tower). -/
def Ares : ℕ := (tw0 206 + M - 4) % M

theorem A_tall (j : ℕ) (hj : 3 ≤ j) : Tall (A j + 4) := by
  have := seq_tall A A_two (fun _ => rfl) (j - 3)
  rwa [show j - 3 + 3 = j by omega] at this

theorem A_mod (j : ℕ) (hj : 3 ≤ j) : A j % M = Ares := by
  obtain ⟨z, hz, e⟩ := A_tall j hj
  have h4 := four_le_tow (show 2 ≤ z by omega)
  rw [show A j = arrow 2 z - 4 by omega, sub_mod' _ _ _ h4 (by have := M_big; omega), ← tw0_eq,
    tw0_stable hz]
  rfl

theorem term_tall (j : ℕ) (hj : 2 ≤ j) : T (j + 1) 1 (A (j + 1)) ≡ C2 Ares j + (V j).2.2 [MOD M] := by
  rw [T_succ_one]
  obtain ⟨z, hz, e⟩ := A_tall (j + 1) (by omega)
  have h1 : C2 (A (j + 1)) j ≡ C2 Ares j [MOD M] := by
    show _ % M = _ % M
    rw [C2_mod, A_mod (j + 1) (by omega)]
  have h2 : T j (A (j + 1) + 2) 0 ≡ (V j).2.2 [MOD M] := by
    have g := V_good j z (Or.inr (Or.inr hz))
    rw [pick_tall _ hz, show arrow 2 z - 2 = A (j + 1) + 2 by omega] at g
    exact modeq_of_mod g
  exact h1.add h2

theorem tt (i j : ℕ) (hij : i + 1 = j) (hi : 2 ≤ i) : T j 1 (A j) ≡ C2 Ares i + (V i).2.2 [MOD M] := by
  subst hij; exact term_tall i hi

theorem add14 {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : ℕ}
    (h0 : a0 ≡ b0 [MOD M]) (h1 : a1 ≡ b1 [MOD M]) (h2 : a2 ≡ b2 [MOD M]) (h3 : a3 ≡ b3 [MOD M])
    (h4 : a4 ≡ b4 [MOD M]) (h5 : a5 ≡ b5 [MOD M]) (h6 : a6 ≡ b6 [MOD M]) (h7 : a7 ≡ b7 [MOD M])
    (h8 : a8 ≡ b8 [MOD M]) (h9 : a9 ≡ b9 [MOD M]) (h10 : a10 ≡ b10 [MOD M]) (h11 : a11 ≡ b11 [MOD M])
    (h12 : a12 ≡ b12 [MOD M]) (h13 : a13 ≡ b13 [MOD M]) :
    a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 + a13 ≡
      b0 + b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 + b13 [MOD M] :=
  ((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add
    h12).add h13

/-- σ's body over a variable, at the definitional height of σ. -/
def sigF (a : ℕ) : ℕ := (fun _ : ℕ → ℕ => 3 * a + 34) A

/-- τ's body over a variable sequence, at the definitional height of τ. -/
def tauF (Af : ℕ → ℕ) : ℕ := (fun _ : ℕ → ℕ => 8574 + ∑ j ∈ range 12, T j 1 (Af j) + CH (Af 12) 12) A

theorem sigma_sigF : sigma = sigF (A 12) := rfl
theorem sigF_eq (a : ℕ) : sigF a = 3 * a + 34 := rfl
theorem tau_tauF : tau = tauF A := rfl

theorem tauF_expand (Af : ℕ → ℕ) : tauF Af = 8574 + T 0 1 (Af 0) + T 1 1 (Af 1) + T 2 1 (Af 2) + T 3 1 (Af 3) +
    T 4 1 (Af 4) + T 5 1 (Af 5) + T 6 1 (Af 6) + T 7 1 (Af 7) + T 8 1 (Af 8) + T 9 1 (Af 9) + T 10 1 (Af 10) +
    T 11 1 (Af 11) + CH (Af 12) 12 := by
  show 8574 + ∑ j ∈ range 12, T j 1 (Af j) + CH (Af 12) 12 = _
  simp only [sum_range_succ, sum_range_zero]
  ring

/-- σ = 3·A₁₂ + 34 ≡ 3·Ares + 34 (mod M). -/
theorem sigma_mod : sigma ≡ 3 * Ares + 34 [MOD M] := by
  rw [sigma_sigF, sigF_eq]
  exact ((Nat.ModEq.refl 3).mul (modeq_of_mod (A_mod 12 (by norm_num)))).add_right 34

set_option maxRecDepth 20000 in
/-- τ mod M from the level table. -/
theorem tau_mod : tau ≡ 8574 + C1 4 + (C2 12 0 + T0part 3) + (C2 65532 1 + (V 1).2.1) + (C2 Ares 2 + (V 2).2.2) +
    (C2 Ares 3 + (V 3).2.2) + (C2 Ares 4 + (V 4).2.2) + (C2 Ares 5 + (V 5).2.2) + (C2 Ares 6 + (V 6).2.2) +
    (C2 Ares 7 + (V 7).2.2) + (C2 Ares 8 + (V 8).2.2) + (C2 Ares 9 + (V 9).2.2) + (C2 Ares 10 + (V 10).2.2) +
    CH Ares 12 [MOD M] := by
  have t0 : T 0 1 (A 0) ≡ C1 4 [MOD M] := by rw [T_zero_one]; rfl
  have t1 : T 1 1 (A 1) ≡ C2 12 0 + T0part 3 [MOD M] := by
    rw [show A 1 = 12 from rfl, T_succ_one]
    have g := T0part_eq 3 (by norm_num)
    rw [tow_three, show (16 : ℕ) - 2 = 12 + 2 by norm_num] at g
    exact (Nat.ModEq.refl _).add (modeq_of_mod g)
  have t2 : T 2 1 (A 2) ≡ C2 65532 1 + (V 1).2.1 [MOD M] := by
    rw [A_two, T_succ_one, show (V 1).2.1 = L1 4 from rfl]
    have g := L1_eq 4 (by norm_num)
    rw [tow_four, show (65536 : ℕ) - 2 = 65532 + 2 by norm_num] at g
    exact (Nat.ModEq.refl _).add (modeq_of_mod g)
  have tc : CH (A 12) 12 ≡ CH Ares 12 [MOD M] := by
    show _ % M = _ % M
    rw [CH_mod, A_mod 12 (by norm_num)]
  rw [tau_tauF, tauF_expand]
  exact add14 (Nat.ModEq.refl 8574) t0 t1 t2 (tt 2 3 rfl le_rfl) (tt 3 4 rfl (by norm_num))
    (tt 4 5 rfl (by norm_num)) (tt 5 6 rfl (by norm_num)) (tt 6 7 rfl (by norm_num)) (tt 7 8 rfl (by norm_num))
    (tt 8 9 rfl (by norm_num)) (tt 9 10 rfl (by norm_num)) (tt 10 11 rfl (by norm_num)) tc

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.L1_eq
#print axioms BeaverStructural.BB7.level_succ
#print axioms BeaverStructural.BB7.V_good
#print axioms BeaverStructural.BB7.sigma_mod
#print axioms BeaverStructural.BB7.tau_mod

