import BeaverStructural.BB7b.RuleMC
import BeaverStructural.BB7b.RuleR4parts

/-! The three loops of the BB(7) machine of October 2026, each by induction on its count from the single pass proved
from the rows: q mini-cycles, j forward passes into the blank tape, i backward passes. -/

namespace BeaverStructural.BB7b

/-- q mini-cycles: the block of q cells is consumed and the left block grows by 3q. -/
theorem miniCycles (q p : ℕ) (X : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (2 * p * q + 3 * q * q + 7 * q)
        ⟨some .E, [], false :: (ones p ++ false :: false :: (ones q ++ X)), h, c⟩ =
      ⟨some .E, [], false :: (ones (p + 3 * q) ++ false :: false :: X), h - 2 * (q : ℤ),
        c + (2 * p * q + 3 * q * q + 7 * q)⟩ := by
  induction q generalizing p h c with
  | zero => simp [Zip.run]
  | succ q ih =>
    rw [show 2 * p * (q + 1) + 3 * (q + 1) * (q + 1) + 7 * (q + 1) =
        (2 * p + 10) + (2 * (p + 3) * q + 3 * q * q + 7 * q) by ring, Zip.run_add]
    have s : Zip.run (2 * p + 10)
        ⟨some .E, [], false :: (ones p ++ false :: false :: (ones (q + 1) ++ X)), h, c⟩ =
        ⟨some .E, [], false :: (ones (p + 3) ++ false :: false :: (ones q ++ X)), h + (-2), c + (2 * p + 10)⟩ :=
      rule_MC p (ones q ++ X) h c
    rw [s, ih (p + 3) (h + (-2)) (c + (2 * p + 10))]
    exact zip_eq rfl rfl (by rw [show p + 3 + 3 * q = p + 3 * (q + 1) by ring]) (by push_cast; ring) (by ring)

/-- j forward passes into the blank tape: the block loses j cells and the trail (0 1)^j is left behind. -/
theorem forwardPasses (j n : ℕ) (L : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (j * j + (2 * n + 7) * j)
        ⟨some .F, L, false :: (ones (j + n + 1) ++ false :: false :: []), h, c⟩ =
      ⟨some .F, tr j ++ L, false :: (ones (n + 1) ++ false :: false :: []), h + 2 * (j : ℤ),
        c + (j * j + (2 * n + 7) * j)⟩ := by
  induction j generalizing L h c with
  | zero => simp [Zip.run]
  | succ j ih =>
    rw [show (j + 1) * (j + 1) + (2 * n + 7) * (j + 1) =
        (2 * (j + n) + 8) + (j * j + (2 * n + 7) * j) by ring, Zip.run_add]
    have s : Zip.run (2 * (j + n) + 8)
        ⟨some .F, L, false :: (ones (j + 1 + n + 1) ++ false :: false :: []), h, c⟩ =
        ⟨some .F, false :: true :: L, false :: (ones (j + n + 1) ++ false :: false :: []), h + 2,
          c + (2 * (j + n) + 8)⟩ := by
      rw [show j + 1 + n + 1 = j + n + 2 by ring]
      exact rule_FWZ (j + n) L h c
    rw [s, ih (false :: true :: L) (h + 2) (c + (2 * (j + n) + 8))]
    exact zip_eq rfl (by simp) rfl (by push_cast; ring) (by ring)

/-- i backward passes: state F on the first cell of (0 1 0 1)^i x L, with 1 0 T to its right; the trail becomes
i digits 1 and the head ends on x. -/
theorem backwardPasses (i : ℕ) (x : Bool) (L T : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (10 * i)
        ⟨some .F, (q4 i ++ x :: L).tail, (q4 i ++ x :: L).headD false :: true :: false :: T, h, c⟩ =
      ⟨some .F, L, x :: true :: false :: (c4 i ++ T), h - 4 * (i : ℤ), c + 10 * i⟩ := by
  induction i generalizing T h c with
  | zero => simp [Zip.run]
  | succ i ih =>
    obtain ⟨y, M, hM⟩ : ∃ y M, q4 i ++ x :: L = y :: M := by
      cases i with
      | zero => exact ⟨x, L, rfl⟩
      | succ i => exact ⟨false, _, rfl⟩
    have ih' := ih (true :: true :: false :: false :: T) (h + (-4)) (c + 10)
    rw [hM] at ih'
    simp only [List.tail_cons, List.headD_cons] at ih'
    rw [show 10 * (i + 1) = 10 + 10 * i by ring, Zip.run_add]
    have e : q4 (i + 1) ++ x :: L = false :: true :: false :: true :: (y :: M) := by
      rw [← hM]; rfl
    have s : Zip.run 10
        ⟨some .F, (q4 (i + 1) ++ x :: L).tail, (q4 (i + 1) ++ x :: L).headD false :: true :: false :: T, h, c⟩ =
        ⟨some .F, M, y :: true :: false :: true :: true :: false :: false :: T, h + (-4), c + 10⟩ := by
      rw [e]
      exact rule_BW y M T h c
    rw [s, ih']
    exact zip_eq rfl rfl (by simp) (by push_cast; ring) (by ring)

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.miniCycles
#print axioms BeaverStructural.BB7b.forwardPasses
#print axioms BeaverStructural.BB7b.backwardPasses
