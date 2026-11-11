import BeaverStructural.BB6.Decrement
import BeaverStructural.BB6.Settlement
import BeaverStructural.BB6.Inner

namespace BeaverStructural.BB6

theorem reset_begin (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run 17 (atLeft ([false,true,false,false,true] ++ l) (false::r) h c) =
      atLeft l ([false,true,true,true,true,false] ++ r) (h-5) (c+17) := by
  simp [atLeft, Zipper.run, Zipper.step, table]
  omega

theorem reset_turn (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run 5 ⟨some .C, true::l, [true,true,true,true,false] ++ r, h, c⟩ =
      ⟨some .A, [true,false,true,false,false,true] ++ l, r, h+5, c+5⟩ := by
  simp [Zipper.run, Zipper.step, table]
  omega

theorem reset_ab (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run 2 ⟨some .A, l, false::false::r, h, c⟩ =
      ⟨some .C, true::true::l, r, h+2, c+2⟩ := by
  simp [Zipper.run, Zipper.step, table]
  omega

theorem positive_outer_tail (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run 29 ⟨some .C, [true,false,false,true] ++ l,
      [false,false,false,false,false] ++ r, h, c⟩ =
      atLeft l ([false,true,true,true,false,false,true,true,true] ++ r) (h-5) (c+29) := by
  simp [atLeft, Zipper.run, Zipper.step, table]
  omega

/-- The original positive-outer reset, for arbitrary inner strip length n,
with both exterior lists retained. No source transition is replaced by arithmetic. -/
theorem reset_strip (L v n b : ℕ) (hv : 0 < v) (hL : v < 2^L)
    (left right : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run (4*n+3*b+63+12*padicValNat 2 v)
      (atLeft (List.replicate n true ++ [false,true,false,false,true] ++
        (counterWord L v).reverse ++ left)
        ([false,true,true,true,false,false] ++ List.replicate (3*(b+1)) true ++
          [false,false,false,false,false] ++ right) h c) =
      atLeft ((oneBlocks b).reverse ++ List.replicate (n+5) true ++
        [false,true,false,false,true] ++ (counterWord L (v-1)).reverse ++ left)
        ([false,true,true,true,false,false,true,true,true] ++ right)
        (h+3*b+5) (c+(4*n+3*b+63+12*padicValNat 2 v)) := by
  let k := padicValNat 2 v
  have cost : 4*n+3*b+63+12*padicValNat 2 v =
      ((((((3*n+17)+(12*k+4))+5)+(n+3))+2)+3*(b+1))+29 := by dsimp [k]; omega
  rw [cost,
    Zipper.run_add (((((3*n+17)+(12*k+4))+5)+(n+3))+2+3*(b+1)) 29,
    Zipper.run_add (((((3*n+17)+(12*k+4))+5)+(n+3))+2) (3*(b+1)),
    Zipper.run_add ((((3*n+17)+(12*k+4))+5)+(n+3)) 2,
    Zipper.run_add (((3*n+17)+(12*k+4))+5) (n+3),
    Zipper.run_add ((3*n+17)+(12*k+4)) 5,
    Zipper.run_add (3*n+17) (12*k+4), Zipper.run_add (3*n) 17]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [q_boundary_strip]
  have beg := reset_begin ((counterWord L v).reverse ++ left)
    (List.replicate n true ++ true::true::true::false::false::
      (List.replicate (3*(b+1)) true ++ false::false::false::false::false::right))
    (h-n) (c+3*n)
  simp only [List.cons_append, List.nil_append] at beg
  rw [beg]
  rw [counter_decrement L v hv hL]
  have turn := reset_turn ((counterWord L (v-1)).reverse ++ left)
    (List.replicate n true ++ true::true::true::false::false::
      (List.replicate (3*(b+1)) true ++ false::false::false::false::false::right))
    (h-n-5+2) (c+3*n+17+12*padicValNat 2 v+4)
  simp only [List.cons_append, List.nil_append] at turn
  rw [turn]
  have ones : List.replicate n true ++ true::true::true::false::false::
      (List.replicate (3*(b+1)) true ++ false::false::false::false::false::right) =
      List.replicate (n+3) true ++ false::false::
      (List.replicate (3*(b+1)) true ++ false::false::false::false::false::right) := by
    conv_rhs => rw [List.replicate_add]
    simp only [List.append_assoc, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
  rw [ones, a1_strip, reset_ab, j_strip]
  have jl := decrement_written b
    (true::(List.replicate (n+3) true ++ true::false::true::false::false::true::
      ((counterWord L (v-1)).reverse ++ left)))
  have shape : writtenJ (b+1) ++ true::true::(List.replicate (n+3) true ++
      true::false::true::false::false::true::((counterWord L (v-1)).reverse ++ left)) =
      [true,false,false,true] ++ ((oneBlocks b).reverse ++
        true::(List.replicate (n+3) true ++ true::false::true::false::false::true::
        ((counterWord L (v-1)).reverse ++ left))) := by
    rw [writtenJ_succ]
    simp only [List.cons_append, List.nil_append, jl]
  rw [shape]
  have tail := positive_outer_tail ((oneBlocks b).reverse ++ true::(List.replicate (n+3) true ++
      true::false::true::false::false::true::((counterWord L (v-1)).reverse ++ left))) right
    (h-n-5+2+5+(n+3)+2+3*(b+1))
    (c+3*n+17+12*padicValNat 2 v+4+5+(n+3)+2+3*(b+1))
  simp only [List.cons_append, List.nil_append] at tail
  simp only [List.cons_append, List.nil_append]
  push_cast
  rw [tail]
  have keep : true::(List.replicate (n+3) true ++ true::false::true::false::false::true::
      ((counterWord L (v-1)).reverse ++ left)) =
      List.replicate (n+5) true ++ false::true::false::false::true::
      ((counterWord L (v-1)).reverse ++ left) := by
    conv_rhs => rw [show n+5=1+(n+3)+1 by omega, List.replicate_add, List.replicate_add]
    simp [List.append_assoc]
  rw [keep]
  rw [show h-(n:ℤ)-5+2+5+((n:ℤ)+3)+2+3*((b:ℤ)+1)-5=h+3*b+5 by omega]
  have hc : c+3*n+17+12*padicValNat 2 v+4+5+(n+3)+2+3*(b+1)+29 =
      c+(3*n+17+(12*k+4)+5+(n+3)+2+3*(b+1)+29) := by dsimp [k]; omega
  rw [hc]


theorem counter_zero_front (L v m a b : ℕ) (h : ℤ) (c : ℕ) :
    counterZipper L v m a 0 b h c =
      atLeft (List.replicate (3*a+m) true ++ [false,true,false,false,true] ++
        (counterWord L v).reverse ++ [true,true,false,true,true,true]) (counterRight b) h c := by
  simp only [counterZipper, counterLeft, counterWord_zero, List.reverse_append,
    List.reverse_replicate, List.append_assoc, List.replicate_add, atLeft]
  rfl

theorem counterWord_low_ones (a b : ℕ) :
    counterWord (a+b) (2^b-1) = List.replicate (3*a) true ++ oneBlocks b := by
  simpa only [Nat.zero_mul, Nat.zero_add, counterWord_zero] using counterWord_one_suffix a b 0

def nextMode (m : ℕ) : ℕ := (m+2)%3
def widthGain (m : ℕ) : ℕ := if m=0 then 1 else 2

theorem reset_width_balance (a m : ℕ) (hm : m < 3) :
    3*(a+widthGain m)+nextMode m = 3*a+m+5 := by
  interval_cases m <;> simp [widthGain, nextMode] <;> omega

theorem counter_reset_front (L v m a b : ℕ) (hm : m < 3) (h : ℤ) (c : ℕ) :
    counterZipper L v (nextMode m) (a+b+widthGain m) (2^b-1) 0 h c =
      atLeft ((oneBlocks b).reverse ++ List.replicate (3*a+m+5) true ++
        [false,true,false,false,true] ++ (counterWord L v).reverse ++
        [true,true,false,true,true,true]) (counterRight 0) h c := by
  rw [show a+b+widthGain m=(a+widthGain m)+b by omega]
  unfold counterZipper counterLeft
  rw [counterWord_low_ones]
  simp only [List.reverse_append, List.reverse_replicate, List.append_assoc]
  have hs : List.replicate (3*(a+widthGain m)) true ++ List.replicate (nextMode m) true =
      List.replicate (3*a+m+5) true := by
    rw [← List.replicate_add, reset_width_balance a m hm]
  rw [← List.append_assoc (List.replicate (3*(a+widthGain m)) true)
    (List.replicate (nextMode m) true), hs]
  rfl

/-- All three original positive-outer modes, including whole-tape identity
and exclusion of every earlier halt, before the newly created inner loop. -/
theorem counter_reset_prefix (L v m a b : ℕ) (hv : 0 < v) (hL : v < 2^L)
    (hm : m < 3) (h : ℤ) (c : ℕ) :
    CountedRun table (12*a+4*m+3*b+63+12*padicValNat 2 v)
      (counterConfig L v m a 0 b h c)
      (counterConfig L (v-1) (nextMode m) (a+b+widthGain m) (2^b-1) 0
        (h+3*b+5) (c+(12*a+4*m+3*b+63+12*padicValNat 2 v))) := by
  let n := 3*a+m
  let lhs := List.replicate n true ++ [false,true,false,false,true] ++
    (counterWord L v).reverse ++ [true,true,false,true,true,true]
  let before := atLeft lhs (counterRight b ++ List.replicate 5 false) h c
  have he : before.config = counterConfig L v m a 0 b h c := by
    rw [counterConfig, counter_zero_front]
    unfold before atLeft lhs n
    simpa only [List.cons_append] using
      config_pad_right (some .E)
        (List.replicate (3*a+m) true ++ [false,true,false,false,true] ++
          (counterWord L v).reverse ++ [true,true,false,true,true,true]).tail
        ((List.replicate (3*a+m) true ++ [false,true,false,false,true] ++
          (counterWord L v).reverse ++ [true,true,false,true,true,true]).headD false :: counterRight b) h c 5
  have hr := reset_strip L v n b hv hL [true,true,false,true,true,true] [] h c
  simp only [List.append_nil] at hr
  have hc : 4*n+3*b+63+12*padicValNat 2 v =
      12*a+4*m+3*b+63+12*padicValNat 2 v := by dsimp [n]; omega
  have hb : before = atLeft lhs
      ([false,true,true,true,false,false] ++ List.replicate (3*(b+1)) true ++
        [false,false,false,false,false]) h c := by
    simp [before, counterRight]
  have hout := counter_reset_front L (v-1) m a b hm (h+3*b+5)
    (c+(12*a+4*m+3*b+63+12*padicValNat 2 v))
  simp only [counterRight] at hout
  apply CountedRun.of_active_endpoint
  · rw [← he, ← Zipper.run_config, hb]
    rw [← hc, hr, hc]
    rw [counterConfig, hout]
    rfl
  · simp [counterConfig, counterZipper, Zipper.config]

end BeaverStructural.BB6
