import BeaverStructural.BB6.Decrement
import BeaverStructural.BB6.Settlement
import BeaverStructural.BB6.Bulk

namespace BeaverStructural.BB6

theorem rayTape_pad_right (l r : List Bool) (n : ℕ) :
    rayTape l (r ++ List.replicate n false) = rayTape l r := by
  funext p
  cases p with
  | negSucc k => rfl
  | ofNat k =>
    simp only [rayTape]
    by_cases hk : k < r.length
    · rw [List.getElem?_append_left hk]
    · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := r) (by omega),
        List.getElem?_replicate]
      split <;> rfl

theorem config_pad_right (q : Option State) (l r : List Bool) (h : ℤ) (c n : ℕ) :
    (⟨q,l,r ++ List.replicate n false,h,c⟩ : Zipper).config =
      (⟨q,l,r,h,c⟩ : Zipper).config := by
  simp only [Zipper.config, rayTape_pad_right]

/-- Inner-counter front with a free left tape, canonical zero right exterior. -/
def innerZipper (a w b : ℕ) (left : List Bool) (head : ℤ) (clock : ℕ) : Zipper :=
  atLeft ((counterWord a w).reverse ++ left) (counterRight b) head clock

theorem inner_once (a w b : ℕ) (hw : 0 < w) (ha : w < 2^a)
    (left : List Bool) (head : ℤ) (clock : ℕ) :
    CountedRun table (12*padicValNat 2 w+12*b+48)
      (innerZipper a w b left head clock).config
      (innerZipper a (w-1) (b+1) left head (clock+12*padicValNat 2 w+12*b+48)).config := by
  let tail := [true,true,true,false,false] ++ List.replicate (3*b+3) true ++ [false,false,false]
  let before := atLeft ((counterWord a w).reverse ++ left) (false::tail) head clock
  have he : before.config = (innerZipper a w b left head clock).config := by
    unfold before innerZipper atLeft tail counterRight
    have hn : 3*(b+1)=3*b+3 := by omega
    rw [hn]
    simpa only [List.cons_append, List.append_assoc] using
      config_pad_right (some .E) (((counterWord a w).reverse ++ left).tail)
        (((counterWord a w).reverse ++ left).headD false ::
          [false,true,true,true,false,false] ++ List.replicate (3*b+3) true) head clock 3
  have hr : before.run (12*padicValNat 2 w+12*b+48) =
      innerZipper a (w-1) (b+1) left head (clock+12*padicValNat 2 w+12*b+48) := by
    rw [show 12*padicValNat 2 w+12*b+48 = (12*padicValNat 2 w+4)+(12*b+44) by omega,
      Zipper.run_add]
    dsimp only [before]
    rw [counter_decrement a w hw ha]
    have ht : tail = [true,true,true,false,false] ++ List.replicate (3*b+3) true ++
        [false,false,false] ++ [] := by simp [tail]
    rw [ht, right_settlement_counter]
    simp only [innerZipper, counterRight, List.append_nil]
    congr 1 <;> omega
  apply CountedRun.of_active_endpoint
  · rw [← he, ← Zipper.run_config, hr]
  · simp [innerZipper, atLeft, Zipper.config]

def innerRunCost : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, b => 12*padicValNat 2 (n+1)+12*b+48 + innerRunCost n (b+1)

/-- Every decrement reads the tape left by its predecessor. The completed
inner loop has a full-state counted result for arbitrary initial n. -/
theorem inner_all (a n b : ℕ) (ha : n < 2^a)
    (left : List Bool) (head : ℤ) (clock : ℕ) :
    CountedRun table (innerRunCost n b)
      (innerZipper a n b left head clock).config
      (innerZipper a 0 (b+n) left head (clock+innerRunCost n b)).config := by
  induction n generalizing b clock with
  | zero => simpa [innerRunCost] using (CountedRun.refl (δ := table) (innerZipper a 0 b left head clock).config)
  | succ n ih =>
    have h₁ := inner_once a (n+1) b (by omega) ha left head clock
    have h₂ := ih (b := b+1) (clock := clock+12*padicValNat 2 (n+1)+12*b+48) (by omega)
    have ht := h₁.trans h₂
    simpa only [innerRunCost, Nat.add_sub_cancel, Nat.add_assoc,
      Nat.add_comm 1 n, Nat.add_left_comm 1 b] using ht

theorem innerRunCost_eq (n b : ℕ) : innerRunCost n b = innerCost n b := by
  induction n generalizing b with
  | zero => simp [innerRunCost, innerCost_zero]
  | succ n ih => rw [innerRunCost, ih, innerCost_succ]

theorem innerZipper_counter (L v m a w b : ℕ) (h : ℤ) (c : ℕ) :
    innerZipper a w b (counterLeft L v m 0 0).reverse h c =
      counterZipper L v m a w b h c := by
  simp [innerZipper, counterZipper, counterLeft, counterWord,
    List.reverse_append, List.append_assoc, atLeft]

/-- Complete source S(L,v,m,a,w,b) -> S(L,v,m,a,0,b+w), preserving the
outer counter, mode, physical head, zero exterior and original primitive cost. -/
theorem counter_inner_all (L v m a w b : ℕ) (hw : w < 2^a) (head : ℤ) (clock : ℕ) :
    CountedRun table (innerCost w b)
      (counterConfig L v m a w b head clock)
      (counterConfig L v m a 0 (b+w) head (clock+innerCost w b)) := by
  have h := inner_all a w b hw (counterLeft L v m 0 0).reverse head clock
  simpa only [innerRunCost_eq, innerZipper_counter, counterConfig] using h

end BeaverStructural.BB6
