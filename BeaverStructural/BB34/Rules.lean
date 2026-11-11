import BeaverStructural.BB34.Machine
import BeaverStructural.BB34.Numbers

/-! The rules of the BB(3,4) machine, each from the rows.
`lemma1`: 3 2^(j+1) <B → 2^(j+1) <B 1 in 2j + 3 steps; `cor2`: its i-fold repetition.
`fixed`: 0^∞ 2^(i+2) <B R → 0^∞ 3 2^(i+1) A> 1 R in 2i + 4 steps.
`inner1`: one unit at k = 1; `level1`: n units at k = 1 in `W1 n a` steps.
`inner`: one unit at k = i + 2 from the rule one level down; `high`: n units at k = j + 2 in `T j n a` steps, for
every right context, by induction on j then n. -/

namespace BeaverStructural.BB34

open BeaverStructural.BB7 (g)

/-- B on the last 2 of 2^(j+1) with x beyond the block: B2, then C across the block. -/
theorem stepBC (j : ℕ) (x : Sy) (L R : List Sy) (h : ℤ) (c : ℕ) :
    Zip.run (j + 1) ⟨some .B, blk .s2 j ++ x :: L, .s2 :: R, h, c⟩ =
      ⟨some .C, L, x :: (blk .s3 j ++ .s1 :: R), h - ((j : ℤ) + 1), c + (j + 1)⟩ := by
  cases j with
  | zero => simp [Zip.run, Zip.step, table]
  | succ m =>
    have s : Zip.run 1 ⟨some .B, blk .s2 (m + 1) ++ x :: L, .s2 :: R, h, c⟩ =
        ⟨some .C, blk .s2 m ++ x :: L, .s2 :: .s1 :: R, h - 1, c + 1⟩ := by
      simp [Zip.run, Zip.step, table]
    have t := chain s (crossC2 m x L (.s1 :: R) (h - 1) (c + 1))
    refine (congrArg (fun k => Zip.run k _) (show m + 1 + 1 = 1 + (m + 1) by ring)).trans (t.trans ?_)
    exact zip_eq rfl rfl rfl (by push_cast; ring) (by ring)

/-- 3 2^(j+1) <B → 2^(j+1) <B 1. -/
theorem lemma1 (j : ℕ) (L R : List Sy) (h : ℤ) (c : ℕ) :
    Zip.run (2 * j + 3) ⟨some .B, blk .s2 j ++ .s3 :: L, .s2 :: R, h, c⟩ =
      ⟨some .B, blk .s2 j ++ L, .s2 :: .s1 :: R, h - 1, c + (2 * j + 3)⟩ := by
  have m1 : Zip.run (j + 1) ⟨some .B, blk .s2 j ++ .s3 :: L, .s2 :: R, h, c⟩ =
      ⟨some .C, L, blk .s3 (j + 1) ++ .s1 :: R, h - ((j : ℤ) + 1), c + (j + 1)⟩ :=
    stepBC j .s3 L R h c
  have m2 := crossC3 (j + 1) L (.s1 :: R) (h - ((j : ℤ) + 1)) (c + (j + 1))
  have m3 : Zip.run 1 ⟨some .C, blk .s2 (j + 1) ++ L, .s1 :: R, h - ((j : ℤ) + 1) + ((j + 1 : ℕ) : ℤ),
        c + (j + 1) + (j + 1)⟩ =
      ⟨some .B, blk .s2 j ++ L, .s2 :: .s1 :: R, h - ((j : ℤ) + 1) + ((j + 1 : ℕ) : ℤ) - 1,
        c + (j + 1) + (j + 1) + 1⟩ := by
    simp [Zip.run, Zip.step, table]
  have all := chain (chain m1 m2) m3
  refine (congrArg (fun k => Zip.run k _) (show 2 * j + 3 = j + 1 + (j + 1) + 1 by ring)).trans (all.trans ?_)
  exact zip_eq rfl rfl rfl (by push_cast; ring) (by ring)

/-- 3^i 2^(j+1) <B → 2^(j+1) <B 1^i. -/
theorem cor2 (i j : ℕ) (L R : List Sy) (h : ℤ) (c : ℕ) :
    Zip.run ((2 * j + 3) * i) ⟨some .B, blk .s2 j ++ (blk .s3 i ++ L), .s2 :: R, h, c⟩ =
      ⟨some .B, blk .s2 j ++ L, .s2 :: (blk .s1 i ++ R), h - (i : ℤ), c + (2 * j + 3) * i⟩ := by
  induction i generalizing R h c with
  | zero => simp [Zip.run]
  | succ i ih =>
    have s : Zip.run (2 * j + 3) ⟨some .B, blk .s2 j ++ (blk .s3 (i + 1) ++ L), .s2 :: R, h, c⟩ =
        ⟨some .B, blk .s2 j ++ (blk .s3 i ++ L), .s2 :: .s1 :: R, h - 1, c + (2 * j + 3)⟩ :=
      lemma1 j (blk .s3 i ++ L) R h c
    have t := chain s (ih (.s1 :: R) (h - 1) (c + (2 * j + 3)))
    refine (congrArg (fun k => Zip.run k _)
      (show (2 * j + 3) * (i + 1) = (2 * j + 3) + (2 * j + 3) * i by ring)).trans (t.trans ?_)
    exact zip_eq rfl rfl (by simp) (by push_cast; ring) (by ring)

/-- 0^∞ 2^(i+2) <B R → 0^∞ 3 2^(i+1) A> 1 R. -/
theorem fixed (i : ℕ) (R : List Sy) (h : ℤ) (c : ℕ) :
    Zip.run (2 * i + 4) ⟨some .B, blk .s2 (i + 1), .s2 :: R, h, c⟩ =
      ⟨some .A, blk .s2 (i + 1) ++ [.s3], .s1 :: R, h, c + (2 * i + 4)⟩ := by
  have m1 : Zip.run 1 ⟨some .B, blk .s2 (i + 1), .s2 :: R, h, c⟩ =
      ⟨some .C, blk .s2 i, .s2 :: .s1 :: R, h - 1, c + 1⟩ := by
    simp [Zip.run, Zip.step, table]
  have m2 := crossC2z i (.s1 :: R) (h - 1) (c + 1)
  have m3 : Zip.run 1 ⟨some .C, [], .s0 :: (blk .s3 (i + 1) ++ .s1 :: R), h - 1 - ((i : ℤ) + 1),
        c + 1 + (i + 1)⟩ =
      ⟨some .B, [.s3], blk .s3 (i + 1) ++ .s1 :: R, h - 1 - ((i : ℤ) + 1) + 1, c + 1 + (i + 1) + 1⟩ := by
    simp [Zip.run, Zip.step, table]
  have m4 : Zip.run 1 ⟨some .B, [.s3], blk .s3 (i + 1) ++ .s1 :: R, h - 1 - ((i : ℤ) + 1) + 1,
        c + 1 + (i + 1) + 1⟩ =
      ⟨some .A, [.s2, .s3], blk .s3 i ++ .s1 :: R, h - 1 - ((i : ℤ) + 1) + 1 + 1, c + 1 + (i + 1) + 1 + 1⟩ := by
    simp [Zip.run, Zip.step, table]
  have m5 := crossA3 i [.s2, .s3] (.s1 :: R) (h - 1 - ((i : ℤ) + 1) + 1 + 1) (c + 1 + (i + 1) + 1 + 1)
  have all := chain (chain (chain (chain m1 m2) m3) m4) m5
  refine (congrArg (fun k => Zip.run k _) (show 2 * i + 4 = 1 + (i + 1) + 1 + 1 + i by ring)).trans
    (all.trans ?_)
  exact zip_eq rfl (by simp) rfl (by push_cast; ring) (by ring)

/-- One unit at k = 1: B(1, n + 1, a) → B(1, n, a + 2). -/
theorem inner1 (a n : ℕ) (X : List Sy) (h : ℤ) (c : ℕ) :
    Zip.run (4 * a + 9) ⟨some .A, .s2 :: blk .s3 (a + 1), .s1 :: (blk .s1 n ++ X), h, c⟩ =
      ⟨some .A, .s2 :: blk .s3 (a + 1 + 1 + 1), blk .s1 n ++ X, h + 1, c + (4 * a + 9)⟩ := by
  have m1 : Zip.run 1 ⟨some .A, .s2 :: blk .s3 (a + 1), .s1 :: (blk .s1 n ++ X), h, c⟩ =
      ⟨some .B, blk .s3 (a + 1), .s2 :: .s3 :: (blk .s1 n ++ X), h - 1, c + 1⟩ := by
    simp [Zip.run, Zip.step, table]
  have m2 := cor2 (a + 1) 0 [] (.s3 :: (blk .s1 n ++ X)) (h - 1) (c + 1)
  simp only [blk_zero, List.nil_append, List.append_nil] at m2
  have m3 : Zip.run 1 ⟨some .B, [], .s2 :: (blk .s1 (a + 1) ++ .s3 :: (blk .s1 n ++ X)),
        h - 1 - ((a + 1 : ℕ) : ℤ), c + 1 + (2 * 0 + 3) * (a + 1)⟩ =
      ⟨some .C, [], .s0 :: .s1 :: (blk .s1 (a + 1) ++ .s3 :: (blk .s1 n ++ X)),
        h - 1 - ((a + 1 : ℕ) : ℤ) - 1, c + 1 + (2 * 0 + 3) * (a + 1) + 1⟩ := by
    simp [Zip.run, Zip.step, table]
  have m4 : Zip.run 1 ⟨some .C, [], .s0 :: .s1 :: (blk .s1 (a + 1) ++ .s3 :: (blk .s1 n ++ X)),
        h - 1 - ((a + 1 : ℕ) : ℤ) - 1, c + 1 + (2 * 0 + 3) * (a + 1) + 1⟩ =
      ⟨some .B, [.s3], blk .s1 (a + 1 + 1) ++ .s3 :: (blk .s1 n ++ X),
        h - 1 - ((a + 1 : ℕ) : ℤ) - 1 + 1, c + 1 + (2 * 0 + 3) * (a + 1) + 1 + 1⟩ := by
    simp [Zip.run, Zip.step, table]
  have m5 := crossB1 (a + 1 + 1) [.s3] (.s3 :: (blk .s1 n ++ X)) (h - 1 - ((a + 1 : ℕ) : ℤ) - 1 + 1)
    (c + 1 + (2 * 0 + 3) * (a + 1) + 1 + 1)
  have m6 : Zip.run 1 ⟨some .B, blk .s3 (a + 1 + 1) ++ [.s3], .s3 :: (blk .s1 n ++ X),
        h - 1 - ((a + 1 : ℕ) : ℤ) - 1 + 1 + ((a + 1 + 1 : ℕ) : ℤ),
        c + 1 + (2 * 0 + 3) * (a + 1) + 1 + 1 + (a + 1 + 1)⟩ =
      ⟨some .A, .s2 :: (blk .s3 (a + 1 + 1) ++ [.s3]), blk .s1 n ++ X,
        h - 1 - ((a + 1 : ℕ) : ℤ) - 1 + 1 + ((a + 1 + 1 : ℕ) : ℤ) + 1,
        c + 1 + (2 * 0 + 3) * (a + 1) + 1 + 1 + (a + 1 + 1) + 1⟩ := by
    simp [Zip.run, Zip.step, table]
  have all := chain (chain (chain (chain (chain m1 m2) m3) m4) m5) m6
  refine (congrArg (fun k => Zip.run k _)
    (show 4 * a + 9 = 1 + (2 * 0 + 3) * (a + 1) + 1 + 1 + (a + 1 + 1) + 1 by ring)).trans (all.trans ?_)
  exact zip_eq rfl (by simp) rfl (by push_cast; ring) (by ring)

/-- n units at k = 1: B(1, n, a) → B(1, 0, a + 2n) in W1 n a steps, every right context. -/
theorem level1 (n : ℕ) : ∀ (a : ℕ) (X : List Sy) (h : ℤ) (c : ℕ), ∃ h' : ℤ,
    Zip.run (W1 n a) ⟨some .A, .s2 :: blk .s3 (a + 1), blk .s1 n ++ X, h, c⟩ =
      ⟨some .A, .s2 :: blk .s3 (a + 2 * n + 1), X, h', c + W1 n a⟩ := by
  induction n with
  | zero => intro a X h c; exact ⟨h, by simp [W1, Zip.run]⟩
  | succ n ih =>
    intro a X h c
    obtain ⟨h', e⟩ := ih (a + 2) X (h + 1) (c + (4 * a + 9))
    refine ⟨h', ?_⟩
    have t := chain (inner1 a n X h c) e
    refine (congrArg (fun k => Zip.run k _) (W1_succ n a)).trans (t.trans ?_)
    exact zip_eq rfl (by rw [show a + 2 + 2 * n + 1 = a + 2 * (n + 1) + 1 by ring]) rfl rfl
      (by rw [W1_succ]; ring)

/-- One unit at k = i + 2 from the rule one level down. -/
theorem inner (i a a' n cost : ℕ) (X : List Sy) (h : ℤ) (c : ℕ)
    (low : ∀ (Y : List Sy) (h : ℤ) (c : ℕ), ∃ h' : ℤ,
      Zip.run cost ⟨some .A, blk .s2 (i + 1) ++ blk .s3 1, blk .s1 (a + 1 + 1) ++ Y, h, c⟩ =
        ⟨some .A, blk .s2 (i + 1) ++ blk .s3 (a' + 1), Y, h', c + cost⟩) :
    ∃ h' : ℤ, Zip.run ((2 * i + 5) * a + 4 * i + 11 + cost)
        ⟨some .A, blk .s2 (i + 1 + 1) ++ blk .s3 (a + 1), .s1 :: (blk .s1 n ++ X), h, c⟩ =
      ⟨some .A, blk .s2 (i + 1 + 1) ++ blk .s3 (a' + 1), blk .s1 n ++ X, h',
        c + ((2 * i + 5) * a + 4 * i + 11 + cost)⟩ := by
  have m1 : Zip.run 1 ⟨some .A, blk .s2 (i + 1 + 1) ++ blk .s3 (a + 1), .s1 :: (blk .s1 n ++ X), h, c⟩ =
      ⟨some .B, blk .s2 (i + 1) ++ blk .s3 (a + 1), .s2 :: .s3 :: (blk .s1 n ++ X), h - 1, c + 1⟩ := by
    simp [Zip.run, Zip.step, table]
  have m2 := cor2 (a + 1) (i + 1) [] (.s3 :: (blk .s1 n ++ X)) (h - 1) (c + 1)
  simp only [List.append_nil] at m2
  have m3 := fixed i (blk .s1 (a + 1) ++ .s3 :: (blk .s1 n ++ X)) (h - 1 - ((a + 1 : ℕ) : ℤ))
    (c + 1 + (2 * (i + 1) + 3) * (a + 1))
  obtain ⟨h4, m4⟩ := low (.s3 :: (blk .s1 n ++ X)) (h - 1 - ((a + 1 : ℕ) : ℤ))
    (c + 1 + (2 * (i + 1) + 3) * (a + 1) + (2 * i + 4))
  have m5 : Zip.run 1 ⟨some .A, blk .s2 (i + 1) ++ blk .s3 (a' + 1), .s3 :: (blk .s1 n ++ X), h4,
        c + 1 + (2 * (i + 1) + 3) * (a + 1) + (2 * i + 4) + cost⟩ =
      ⟨some .A, .s2 :: (blk .s2 (i + 1) ++ blk .s3 (a' + 1)), blk .s1 n ++ X, h4 + 1,
        c + 1 + (2 * (i + 1) + 3) * (a + 1) + (2 * i + 4) + cost + 1⟩ := by
    simp [Zip.run, Zip.step, table]
  refine ⟨h4 + 1, ?_⟩
  have all := chain (chain (chain (chain m1 m2) m3) m4) m5
  refine (congrArg (fun k => Zip.run k _)
    (show (2 * i + 5) * a + 4 * i + 11 + cost = 1 + (2 * (i + 1) + 3) * (a + 1) + (2 * i + 4) + cost + 1 by
      ring)).trans (all.trans ?_)
  exact zip_eq rfl rfl rfl rfl (by ring)

/-- n units at k = j + 2: B(j + 2, n, a) → B(j + 2, 0, g_j^n(a)) in T j n a steps, every right context. -/
theorem high (j : ℕ) : ∀ (n a : ℕ) (X : List Sy) (h : ℤ) (c : ℕ), ∃ h' : ℤ,
    Zip.run (T j n a) ⟨some .A, blk .s2 (j + 1 + 1) ++ blk .s3 (a + 1), blk .s1 n ++ X, h, c⟩ =
      ⟨some .A, blk .s2 (j + 1 + 1) ++ blk .s3 ((g j)^[n] a + 1), X, h', c + T j n a⟩ := by
  induction j with
  | zero =>
    intro n
    induction n with
    | zero => intro a X h c; exact ⟨h, by simp [T_none, Zip.run]⟩
    | succ n ih =>
      intro a X h c
      have low : ∀ (Y : List Sy) (h : ℤ) (c : ℕ), ∃ h' : ℤ,
          Zip.run (W1 (a + 2) 0) ⟨some .A, blk .s2 (0 + 1) ++ blk .s3 1, blk .s1 (a + 1 + 1) ++ Y, h, c⟩ =
            ⟨some .A, blk .s2 (0 + 1) ++ blk .s3 (g 0 a + 1), Y, h', c + W1 (a + 2) 0⟩ := by
        intro Y h c
        obtain ⟨h', e⟩ := level1 (a + 2) 0 Y h c
        refine ⟨h', e.trans (zip_eq rfl ?_ rfl rfl rfl)⟩
        show Sy.s2 :: blk .s3 (0 + 2 * (a + 2) + 1) = Sy.s2 :: blk .s3 (2 * a + 4 + 1)
        rw [show 0 + 2 * (a + 2) + 1 = 2 * a + 4 + 1 by ring]
      obtain ⟨h1, e1⟩ := inner 0 a (g 0 a) n (W1 (a + 2) 0) X h c low
      obtain ⟨h2, e2⟩ := ih (g 0 a) X h1 (c + ((2 * 0 + 5) * a + 4 * 0 + 11 + W1 (a + 2) 0))
      refine ⟨h2, ?_⟩
      have hT : T 0 (n + 1) a = (2 * 0 + 5) * a + 4 * 0 + 11 + W1 (a + 2) 0 + T 0 n (g 0 a) := by
        rw [T_zero_succ, C1_eq]
      refine (congrArg (fun k => Zip.run k _) hT).trans ((chain e1 e2).trans ?_)
      exact zip_eq rfl (by rw [Function.iterate_succ_apply]) rfl rfl (by rw [hT]; ring)
  | succ j ihj =>
    intro n
    induction n with
    | zero => intro a X h c; exact ⟨h, by simp [T_none, Zip.run]⟩
    | succ n ih =>
      intro a X h c
      obtain ⟨h1, e1⟩ := inner (j + 1) a (g (j + 1) a) n (T j (a + 2) 0) X h c
        (fun Y h c => ihj (a + 2) 0 Y h c)
      obtain ⟨h2, e2⟩ := ih (g (j + 1) a) X h1
        (c + ((2 * (j + 1) + 5) * a + 4 * (j + 1) + 11 + T j (a + 2) 0))
      refine ⟨h2, ?_⟩
      have hT : T (j + 1) (n + 1) a =
          (2 * (j + 1) + 5) * a + 4 * (j + 1) + 11 + T j (a + 2) 0 + T (j + 1) n (g (j + 1) a) := by
        rw [T_succ_succ, C2_eq]
      refine (congrArg (fun k => Zip.run k _) hT).trans ((chain e1 e2).trans ?_)
      exact zip_eq rfl (by rw [Function.iterate_succ_apply]) rfl rfl (by rw [hT]; ring)

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.cor2
#print axioms BeaverStructural.BB34.fixed
#print axioms BeaverStructural.BB34.level1
#print axioms BeaverStructural.BB34.high
