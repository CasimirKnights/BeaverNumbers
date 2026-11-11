import BeaverStructural.BB6.Strips
import BeaverStructural.BB6.CounterTape

namespace BeaverStructural.BB6

/-- Zero-outer, mode-zero configuration in the same whole-tape zipper frame. -/
def terminalStart (L a b : ℕ) (h : ℤ) (c : ℕ) : Zipper :=
  atLeft (List.replicate (3*a) true ++ [false,true,false,false,true] ++
    List.replicate (3*L) true ++ [true,true,false,true,true,true])
    ([false,true,true,true,false,false] ++ List.replicate (3*(b+1)) true) h c

theorem terminalStart_eq (L a b : ℕ) (h : ℤ) (c : ℕ) :
    terminalStart L a b h c = counterZipper L 0 0 a 0 b h c := by
  simp [terminalStart, counterZipper, counterLeft, counterRight, counterWord_zero,
    List.reverse_append, List.reverse_replicate, atLeft, List.append_assoc]

/-- First whole-strip crossing of the zero inner counter. -/
theorem terminal_first_strip (L a b : ℕ) (h : ℤ) (c : ℕ) :
    (terminalStart L a b h c).run (3*(3*a)) =
    atLeft ([false,true,false,false,true] ++ List.replicate (3*L) true ++
      [true,true,false,true,true,true])
      (false :: (List.replicate (3*a) true ++
        [true,true,true,false,false] ++ List.replicate (3*(b+1)) true))
      (h-3*a) (c+9*a) := by
  unfold terminalStart
  rw [show List.replicate (3*a) true ++ [false,true,false,false,true] ++
        List.replicate (3*L) true ++ [true,true,false,true,true,true] =
      List.replicate (3*a) true ++ ([false,true,false,false,true] ++
        List.replicate (3*L) true ++ [true,true,false,true,true,true]) by
        simp only [List.append_assoc]]
  simp only [List.cons_append, List.nil_append]
  rw [q_boundary_strip]
  simp only [List.append_assoc]
  congr 1; ring

/-- P then R, before the long outer-boundary crossing. -/
theorem terminal_pr (l r : List Bool) (h : ℤ) (c : ℕ) :
    (atLeft ([false,true,false,false,true] ++ l) (false::r) h c).run 8 =
      atLeft ([true,true,true] ++ l) (false::true::false::r) (h-2) (c+8) := by
  simp [atLeft, Zipper.run, Zipper.step, table]
  omega

theorem terminal_outer_word (L : ℕ) :
    [true,true,true] ++ List.replicate (3*L) true ++ [true,true,false,true,true,true] =
      List.replicate (3*L+5) true ++ [false,true,true,true] := by
  rw [show 3*L+5 = 3+3*L+2 by omega, List.replicate_add, List.replicate_add]
  simp [List.append_assoc]

theorem terminal_pqq (r : List Bool) (h : ℤ) (c : ℕ) :
    (atLeft [false,true,true,true] (false::r) h c).run 8 =
      atLeft [] (false::true::true::false::false::r) (h-4) (c+8) := by
  simp [atLeft, Zipper.run, Zipper.step, table]
  omega

def terminalBoundary : List Bool := [true,false,false,true,true,true,false,true,true,true]

theorem terminal_rebuild (r : List Bool) (h : ℤ) (c : ℕ) :
    (atLeft [] ([false,true,true,false,false,true,true,true] ++ r) h c).run 13 =
      ⟨some .C, terminalBoundary, r, h+9, c+13⟩ := by
  simp [atLeft, Zipper.run, Zipper.step, table, terminalBoundary]
  omega

theorem terminal_m (l r : List Bool) (h : ℤ) (c : ℕ) :
    (Zipper.mk (some .C) (true::false::false::l) (false::r) h c).run 6 =
      ⟨some .C, true::true::true::l, true::r, h, c+6⟩ := by
  simp [Zipper.run, Zipper.step, table]

theorem terminal_last (l r : List Bool) (h : ℤ) (c : ℕ) :
    (Zipper.mk (some .C) l (true::false::false::true::r) h c).run 4 =
      ⟨none, true::true::true::false::l, r, h+4, c+4⟩ := by
  simp [Zipper.run, Zipper.step, table]
  omega

def zeroOuterStart (L n b : ℕ) (h : ℤ) (c : ℕ) : Zipper :=
  atLeft (List.replicate n true ++ ([false,true,false,false,true] ++
    List.replicate (3*L) true ++ [true,true,false,true,true,true]))
    (false :: ([true,true,true,false,false] ++ List.replicate (3*(b+1)) true)) h c

def rightPacket (b : ℕ) : List Bool :=
  [true,true,true,false,false] ++ List.replicate (3*(b+1)) true

/-- The complete zero-outer boundary rebuild through M, before the final inner J strip. -/
theorem zero_outer_prefix (L n b : ℕ) (h : ℤ) (c : ℕ) :
    (zeroOuterStart L n b h c).run (3*n+12*L+53) =
      ⟨some .C, [true,true,true] ++ writtenJ L ++ terminalBoundary,
        true :: (List.replicate n true ++ rightPacket b), h-n+1, c+3*n+12*L+53⟩ := by
  let R := List.replicate n true ++ rightPacket b
  have hR : List.replicate n true ++
      ([true,true,true,false,false] ++ List.replicate (3*(b+1)) true) = R := rfl
  have s1 := q_boundary_strip n
    ([false,true,false,false,true] ++ List.replicate (3*L) true ++ [true,true,false,true,true,true])
    ([true,true,true,false,false] ++ List.replicate (3*(b+1)) true) h c
  have s2 := terminal_pr (List.replicate (3*L) true ++ [true,true,false,true,true,true])
    R (h-n) (c+3*n)
  have hs2 : [true,true,true] ++ (List.replicate (3*L) true ++ [true,true,false,true,true,true]) =
      List.replicate (3*L+5) true ++ [false,true,true,true] := by
    simpa only [List.append_assoc] using terminal_outer_word L
  have s3 := q_boundary_strip (3*L+5) [false,true,true,true]
    (true::false::R) (h-n-2) (c+3*n+8)
  have s4 := terminal_pqq (List.replicate (3*L+5) true ++ true::false::R)
    (h-n-2-(3*L+5)) (c+3*n+8+3*(3*L+5))
  have hr : false::true::true::false::false::(List.replicate (3*L+5) true ++ true::false::R) =
      [false,true,true,false,false,true,true,true] ++
        (List.replicate (3*(L+1)) true ++ false::R) := by
    rw [show 3*L+5 = 3+(3*L+2) by omega, List.replicate_add]
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
    rw [show 3*(L+1) = 3*L+2+1 by omega, List.replicate_add]
    simp [List.append_assoc]
    rw [show 3*L+2 = 2+3*L by omega, List.replicate_add]
    simp
  have s5 := terminal_rebuild (List.replicate (3*(L+1)) true ++ false::R)
    (h-n-2-(3*L+5)-4) (c+3*n+8+3*(3*L+5)+8)
  have s6 := j_strip (L+1) terminalBoundary (false::R)
    (h-n-2-(3*L+5)-4+9) (c+3*n+8+3*(3*L+5)+8+13)
  have s7 := terminal_m (writtenJ L ++ terminalBoundary) R
    (h-n-2-(3*L+5)-4+9+3*(L+1)) (c+3*n+8+3*(3*L+5)+8+13+3*(L+1))
  rw [show 3*n+12*L+53 = 3*n+8+3*(3*L+5)+8+13+3*(L+1)+6 by omega]
  simp only [Zipper.run_add]
  rw [show zeroOuterStart L n b h c =
      atLeft (List.replicate n true ++
        ([false,true,false,false,true] ++ List.replicate (3*L) true ++ [true,true,false,true,true,true]))
        (false::([true,true,true,false,false] ++ List.replicate (3*(b+1)) true)) h c from rfl]
  rw [s1, hR]
  simp only [List.append_assoc]
  rw [s2]
  rw [hs2]
  push_cast at s3 s6
  rw [s3, s4, hr, s5, s6, writtenJ_succ]
  simp only [List.cons_append, List.nil_append]
  rw [s7]
  rw [show h-n-2-(3*(L:ℤ)+5)-4+9+3*((L:ℤ)+1) = h-n+1 by omega]
  rw [show c+3*n+8+3*(3*L+5)+8+13+3*(L+1)+6 = c+3*n+12*L+53 by omega]

theorem zeroOuterStart_eq (L m a b : ℕ) (h : ℤ) (c : ℕ) :
    zeroOuterStart L (3*a+m) b h c = counterZipper L 0 m a 0 b h c := by
  simp [zeroOuterStart, counterZipper, counterLeft, counterRight, counterWord_zero,
    List.reverse_append, List.reverse_replicate, atLeft, List.append_assoc, List.replicate_add, -List.replicate_append_replicate]

def commonLeft (L a : ℕ) : List Bool :=
  writtenJ (a+1) ++ [true,true,true] ++ writtenJ L ++ terminalBoundary

theorem zero_outer_common (L m a b : ℕ) (h : ℤ) (c : ℕ) :
    (counterZipper L 0 m a 0 b h c).run (12*L+12*a+3*m+56) =
      ⟨some .C, commonLeft L a,
        List.replicate (m+1) true ++ [false,false] ++ List.replicate (3*(b+1)) true,
        h-m+4, c+12*L+12*a+3*m+56⟩ := by
  have hr : true :: (List.replicate (3*a+m) true ++ rightPacket b) =
      List.replicate (3*(a+1)) true ++
        (List.replicate (m+1) true ++ [false,false] ++ List.replicate (3*(b+1)) true) := by
    change List.replicate 1 true ++ (List.replicate (3*a+m) true ++
      (List.replicate 3 true ++ ([false,false] ++ List.replicate (3*(b+1)) true))) = _
    simp only [← List.append_assoc, ← List.replicate_add]
    rw [show 1+(3*a+m+3) = 3*(a+1)+(m+1) by omega]
  rw [← zeroOuterStart_eq]
  rw [show 12*L+12*a+3*m+56 = (3*(3*a+m)+12*L+53)+3*(a+1) by omega,
      Zipper.run_add, zero_outer_prefix, hr, j_strip]
  unfold commonLeft
  simp only [List.append_assoc]
  congr 1 <;> push_cast <;> omega

def terminalZipper (L a b : ℕ) (h : ℤ) (c : ℕ) : Zipper :=
  ⟨none, [true,true,true,false] ++ commonLeft L a,
    List.replicate (3*b+2) true, h+8, c+12*L+12*a+60⟩

/-- All-parameter complete terminal law, with the original final B1 included. -/
theorem zero_outer_halt (L a b : ℕ) (h : ℤ) (c : ℕ) :
    (counterZipper L 0 0 a 0 b h c).run (12*L+12*a+60) = terminalZipper L a b h c := by
  rw [show 12*L+12*a+60 = (12*L+12*a+3*0+56)+4 by omega,
    Zipper.run_add, zero_outer_common L 0 a b h c]
  have hb : 3*(b+1) = 1+(3*b+2) := by omega
  have hrep : List.replicate (3*(b+1)) true = true::List.replicate (3*b+2) true := by
    rw [hb, Nat.add_comm 1]
    rfl
  simp only [Nat.zero_add, List.replicate_one, List.cons_append, List.nil_append, Int.natCast_zero,
    sub_zero, hrep]
  change (Zipper.mk (some .C) (commonLeft L a)
    (true::false::false::true::List.replicate (3*b+2) true) (h+4)
    (c+12*L+12*a+3*0+56)).run 4 = _
  rw [terminal_last]
  unfold terminalZipper
  congr 1; omega

/-- Counted terminal source theorem; no earlier halt is allowed by its exact clock gain. -/
theorem counter_terminal (L a b : ℕ) (h : ℤ) (c : ℕ) :
    CountedRun table (12*L+12*a+60) (counterConfig L 0 0 a 0 b h c)
      (terminalZipper L a b h c).config := by
  apply CountedRun.of_clock_endpoint
  · rw [counterConfig, ← Zipper.run_config, zero_outer_halt]
  · simp only [terminalZipper, counterConfig, counterZipper, Zipper.config]
    omega

/-- First part of the mode-one reset tail, retaining arbitrary left context. -/
theorem reset_tail_start (l r : List Bool) (h : ℤ) (c : ℕ) :
    (Zipper.mk (some .C) l ([true,true,false,false,true,true,true] ++ r) h c).run 9 =
      ⟨some .C, [true,false,false,true,true,true,false] ++ l, r, h+7, c+9⟩ := by
  simp [Zipper.run, Zipper.step, table]
  omega

/-- Final mode-one reset tail, including all newly created right cells. -/
theorem reset_tail_finish (l : List Bool) (h : ℤ) (c : ℕ) :
    (Zipper.mk (some .C) ([true,false,false,true] ++ l) [] h c).run 29 =
      atLeft l (counterRight 0) (h-5) (c+29) := by
  simp [Zipper.run, Zipper.step, table, atLeft, counterRight]
  omega

def reverseBlocks (n : ℕ) : List Bool :=
  (List.replicate n [false,false,true]).flatten

theorem reverseBlocks_succ (n : ℕ) :
    reverseBlocks (n+1) = [false,false,true] ++ reverseBlocks n := by
  simp [reverseBlocks, List.replicate_succ]

theorem writtenJ_rotate (n : ℕ) :
    writtenJ n ++ [true] = true :: reverseBlocks n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [writtenJ_succ, List.append_assoc, ih, reverseBlocks_succ]
    rfl

theorem reverseBlocks_eq (b : ℕ) :
    reverseBlocks b = (counterWord b (2^b-1)).reverse := by
  rw [counterWord_max]
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [reverseBlocks_succ, oneBlocks_succ, List.reverse_append, ← ih]
    rfl

/-- Full mode-one reset tail, using the original row word and no halting oracle. -/
theorem reset_tail (b : ℕ) (l : List Bool) (h : ℤ) (c : ℕ) :
    (Zipper.mk (some .C) l
      ([true,true,false,false] ++ List.replicate (3*(b+1)) true) h c).run (3*b+38) =
      atLeft ((counterWord b (2^b-1)).reverse ++ [true,true,false] ++ l)
        (counterRight 0) (h+3*b+2) (c+3*b+38) := by
  have hin : [true,true,false,false] ++ List.replicate (3*(b+1)) true =
      [true,true,false,false,true,true,true] ++ List.replicate (3*b) true := by
    rw [show 3*(b+1)=3+3*b by omega, List.replicate_add]
    rfl
  have hout : writtenJ b ++ ([true,false,false,true,true,true,false] ++ l) =
      [true,false,false,true] ++ (reverseBlocks b ++ [true,true,false] ++ l) := by
    have hx := writtenJ_rotate (b+1)
    rw [← writtenJ_append] at hx
    rw [reverseBlocks_succ] at hx
    have hxa := congrArg (fun w : List Bool => w ++ [true,true,false] ++ l) hx
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using hxa
  rw [show 3*b+38=9+3*b+29 by omega, Zipper.run_add, Zipper.run_add, hin, reset_tail_start]
  rw [show List.replicate (3*b) true = List.replicate (3*b) true ++ [] by simp]
  rw [j_strip, hout, reset_tail_finish, reverseBlocks_eq]
  congr 1 <;> push_cast <;> omega

end BeaverStructural.BB6
