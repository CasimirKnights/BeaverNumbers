import BeaverStructural.BB7.Champion
/-! The halting score: after the halting row the tape of the BB(7) champion has exactly σ = 3·A₁₂ + 34 cells holding 1.
`ncard_nat`, `ncard_ray`, `ncard_shift`: the cells holding 1 on the tape of a zipper are counted by the trues in its
two lists. -/

namespace BeaverStructural.BB7

open Finset

theorem fin_getD (r : List Bool) : {n : ℕ | r[n]?.getD false = true}.Finite := by
  refine (Set.finite_lt_nat r.length).subset ?_
  intro n hn
  by_contra h
  simp only [Set.mem_setOf_eq, not_lt] at h hn
  simp [List.getElem?_eq_none h] at hn

theorem ncard_nat (r : List Bool) : Set.ncard {n : ℕ | r[n]?.getD false = true} = r.count true := by
  induction r with
  | nil => simp
  | cons b r ih =>
    have hset : {n : ℕ | (b :: r)[n]?.getD false = true} =
        {n : ℕ | n = 0 ∧ b = true} ∪ Nat.succ '' {n | r[n]?.getD false = true} := by
      ext n
      cases n with
      | zero => simp
      | succ n => simp
    have hd : Disjoint {n : ℕ | n = 0 ∧ b = true} (Nat.succ '' {n | r[n]?.getD false = true}) := by
      rw [Set.disjoint_left]
      rintro x ⟨rfl, -⟩ ⟨y, -, hy⟩
      exact Nat.succ_ne_zero y hy
    have hf0 : {n : ℕ | n = 0 ∧ b = true}.Finite := (Set.finite_singleton 0).subset (fun n hn => hn.1)
    rw [hset, Set.ncard_union_eq hd hf0 ((fin_getD r).image _),
      Set.ncard_image_of_injective _ Nat.succ_injective, ih]
    cases b
    · simp
    · have : {n : ℕ | n = 0 ∧ true = true} = {0} := by ext n; simp
      rw [this, Set.ncard_singleton]
      simp [List.count_cons]
      omega

theorem ncard_ray (l r : List Bool) :
    Set.ncard {i : ℤ | BB6.rayTape l r i = true} = r.count true + l.count true := by
  have hset : {i : ℤ | BB6.rayTape l r i = true} =
      (fun n : ℕ => (n : ℤ)) '' {n | r[n]?.getD false = true} ∪
        Int.negSucc '' {n | l[n]?.getD false = true} := by
    ext i
    cases i with
    | ofNat n =>
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
      constructor
      · intro h; exact Or.inl ⟨n, h, rfl⟩
      · rintro (⟨m, hm, e⟩ | ⟨m, -, e⟩)
        · have : m = n := Int.ofNat.inj e
          subst this; exact hm
        · exact absurd e (by simp)
    | negSucc n =>
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
      constructor
      · intro h; exact Or.inr ⟨n, h, rfl⟩
      · rintro (⟨m, -, e⟩ | ⟨m, hm, e⟩)
        · exact absurd e (by omega)
        · cases e; exact hm
  have hd : Disjoint ((fun n : ℕ => (n : ℤ)) '' {n | r[n]?.getD false = true})
      (Int.negSucc '' {n | l[n]?.getD false = true}) := by
    rw [Set.disjoint_left]
    rintro x ⟨m, -, rfl⟩ ⟨k, -, e⟩
    dsimp only at e; omega
  rw [hset, Set.ncard_union_eq hd ((fin_getD r).image _) ((fin_getD l).image _),
    Set.ncard_image_of_injective _ Nat.cast_injective,
    Set.ncard_image_of_injective _ (fun a b h => Int.negSucc.inj h), ncard_nat, ncard_nat]

theorem ncard_shift (l r : List Bool) (h : ℤ) :
    Set.ncard {p : ℤ | BB6.rayTape l r (p - h) = true} = r.count true + l.count true := by
  have : {p : ℤ | BB6.rayTape l r (p - h) = true} = (fun i => i + h) '' {i : ℤ | BB6.rayTape l r i = true} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hp; exact ⟨p - h, hp, by ring⟩
    · rintro ⟨i, hi, rfl⟩; simpa using hi
  rw [this, Set.ncard_image_of_injective _ (add_left_injective h), ncard_ray]

theorem count_pw (m : ℕ) (X : List Bool) : (pw true false m ++ X).count true = m + X.count true := by
  induction m with
  | zero => simp
  | succ m ih => simp [ih]; omega

theorem count_r4Right (n : ℕ) : (r4Right n).count true = n + 32 := by
  simp only [r4Right, List.count_cons, count_pw]
  simp

theorem halts_config {S a : ℕ} {h' : ℤ} (e : Zip.run S blankZip = bZip a (List.replicate 12 0) h' S) :
    (Zip.run (S + CH a 12) blankZip).config = (haltZip a h' S).config := by
  rw [Zip.run_add, e]; exact halt_from _ _ _

theorem ones_haltZip (a : ℕ) (h : ℤ) (c : ℕ) :
    Set.ncard {p : ℤ | (haltZip a h c).config.tape p = true} = 3 * a + 34 := by
  simp only [haltZip, Zip.config]
  rw [ncard_shift, count_r4Right]
  simp

/-- After the halting row, the champion's tape has exactly σ = 3·A₁₂ + 34 cells holding 1. -/
theorem champion_sigma : Set.ncard {p : ℤ | ((BeaverStructural.step table)^[tau] blank).tape p = true} = sigma := by
  obtain ⟨h', e⟩ := ladder_top
  rw [← blankZip_config, ← Zip.run_config, tau_tauF, tauF_body, halts_config e, ones_haltZip, sigma_sigF, sigF_eq]

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.ncard_shift
#print axioms BeaverStructural.BB7.champion_sigma
