import BeaverStructural.BB7.Defs
import BeaverStructural.BB7.RulesR12
/-! The configuration family B(a; b, c, …, z) = 0^∞ 111 (01)^(3z+1) 1 ⋯ 1 (01)^(3b+1) 1 (01)^0 1 (01)^(3a+1) 0011100 A> 0^∞
as a zipper (left nearest cell first, the head on the blank right of the word), P(m, n) = R1 applied m times, and the
mid-level rules composed from the low-level rules. -/

namespace BeaverStructural.BB7

/-- The blocks b, c, …, z of a B configuration, nearest first, ending in 111 against the blank. -/
def blk : List ℕ → List Bool
  | [] => [true, true]
  | b :: bs => pw true false (3 * b + 1) ++ true :: blk bs

def bLeft (a : ℕ) (bs : List ℕ) : List Bool :=
  false :: false :: true :: true :: true :: false :: false :: (pw true false (3 * a + 1) ++ true :: true :: blk bs)

/-- B(a; bs) with the head at h and clock c. -/
def bZip (a : ℕ) (bs : List ℕ) (h : ℤ) (c : ℕ) : Zip := ⟨some .A, bLeft a bs, [], h, c⟩

theorem pw_add (a b : Bool) (m k : ℕ) (X : List Bool) : pw a b (m + k) ++ X = pw a b m ++ (pw a b k ++ X) := by
  induction m with
  | zero => simp
  | succ m ih => rw [show m + 1 + k = (m + k) + 1 by ring]; simp [ih]

/-- P(m, n): 01^m 1 01^n 0011100 A> → 1 01^(n+2m) 0011100 A> in 4mn + 4m² + 38m steps. -/
theorem ruleP (m : ℕ) : ∀ (n : ℕ) (L : List Bool) (h : ℤ) (c : ℕ),
    Zip.run (4 * m * n + 4 * m ^ 2 + 38 * m)
      ⟨some .A, false :: false :: true :: true :: true :: false :: false ::
        (pw true false n ++ true :: (pw true false m ++ L)), [], h, c⟩ =
      ⟨some .A, false :: false :: true :: true :: true :: false :: false ::
        (pw true false (n + 2 * m) ++ true :: L), [], h + 2 * (m : ℤ), c + (4 * m * n + 4 * m ^ 2 + 38 * m)⟩ := by
  induction m with
  | zero => intro n L h c; simp [Zip.run]
  | succ m ih =>
    intro n L h c
    have e := rule_R1 n (pw true false m ++ L) h c
    have e2 := ih (n + 2) L (h + 2) (c + (4 * n + 42))
    have hl : pw true false n ++ true :: (pw true false (m + 1) ++ L) =
        pw true false n ++ (true :: (true :: (false :: (pw true false m ++ L)))) := by simp
    rw [hl]
    refine (congrArg (fun t => Zip.run t _) (show 4 * (m + 1) * n + 4 * (m + 1) ^ 2 + 38 * (m + 1) =
      (4 * n + 42) + (4 * m * (n + 2) + 4 * m ^ 2 + 38 * m) by ring)).trans ((chain e e2).trans ?_)
    exact zip_eq rfl (by rw [show n + 2 + 2 * m = n + 2 * (m + 1) by ring]) rfl (by push_cast; ring) (by ring)

/-- B(a; b+1, rest) → B(2a+4; b, rest) in C1(a) steps. -/
theorem mid1 (a b : ℕ) (rest : List ℕ) (h : ℤ) (c : ℕ) :
    Zip.run (C1 a) (bZip a ((b + 1) :: rest) h c) = bZip (2 * a + 4) (b :: rest) (h + (6 * a + 18)) (c + C1 a) := by
  have e1 := rule_R2 (3 * a + 1) (pw true false (3 * b + 1) ++ true :: blk rest) h c
  have e2 := ruleP (3 * a + 6) 1 (true :: (pw true false (3 * b + 1) ++ true :: blk rest)) (h + 6)
    (c + (16 * (3 * a + 1) + 178))
  have l0 : bLeft a ((b + 1) :: rest) = false :: false :: true :: true :: true :: false :: false ::
      (pw true false (3 * a + 1) ++ true :: true :: (pw true false 3 ++
        (pw true false (3 * b + 1) ++ true :: blk rest))) := by
    simp only [bLeft, blk]
    rw [show pw true false (3 * (b + 1) + 1) ++ true :: blk rest =
      pw true false 3 ++ (pw true false (3 * b + 1) ++ true :: blk rest) by
        rw [show 3 * (b + 1) + 1 = 3 + (3 * b + 1) by ring, pw_add]]
  have l1 : false :: false :: true :: true :: true :: false :: false :: true :: false :: true ::
      (pw true false (3 * a + 1 + 5) ++ true :: (pw true false (3 * b + 1) ++ true :: blk rest)) =
      false :: false :: true :: true :: true :: false :: false ::
        (pw true false 1 ++ true :: (pw true false (3 * a + 6) ++ true :: (pw true false (3 * b + 1) ++
          true :: blk rest))) := by
    simp
  unfold bZip
  rw [l0]
  rw [l1] at e1
  refine (congrArg (fun t => Zip.run t _) (show C1 a = (16 * (3 * a + 1) + 178) +
    (4 * (3 * a + 6) * 1 + 4 * (3 * a + 6) ^ 2 + 38 * (3 * a + 6)) by simp only [C1]; ring)).trans
    ((chain e1 e2).trans ?_)
  refine zip_eq rfl ?_ rfl (by push_cast; ring) (by simp only [C1]; ring)
  simp only [bLeft, blk]
  rw [show 1 + 2 * (3 * a + 6) = 3 * (2 * a + 4) + 1 by ring]

theorem blk_zeros (k : ℕ) (X : List ℕ) :
    blk (List.replicate k 0 ++ X) = (List.replicate k [true, false, true]).flatten ++ blk X := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, blk, ih]

theorem pw_three_succ (m : ℕ) (X : List Bool) :
    pw true false (3 * (m + 1) + 1) ++ X = pw true false 3 ++ (pw true false (3 * m + 1) ++ X) := by
  rw [show 3 * (m + 1) + 1 = 3 + (3 * m + 1) by ring, pw_add]

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.ruleP
#print axioms BeaverStructural.BB7.mid1
