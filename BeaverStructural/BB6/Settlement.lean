import BeaverStructural.BB6.Strips

/-! The complete right settlement J V A1^n Z Q^(n+2) P Q^3.
The theorem is stronger than the counter application n=3b+3: both exteriors
are arbitrary and all writes/head/primitive ticks are retained. -/
namespace BeaverStructural.BB6

theorem settlement_prefix (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run 11 ⟨some .C, true::l, [true,true,true,false,false] ++ r, h, c⟩ =
      ⟨some .A, [true,false,true,true,true,true] ++ l, r, h+5, c+11⟩ := by
  simp [Zipper.run, Zipper.step, table]
  omega

theorem settlement_z (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run 4 ⟨some .A, l, false::false::false::r, h, c⟩ =
      ⟨some .E, l, true::false::true::r, h, c+4⟩ := by
  simp [Zipper.run, Zipper.step, table]

theorem settlement_tail (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run 11 (atLeft ([false,true,true,true,true] ++ l) (false::r) h c) =
      atLeft l ([false,true,true,true,false,false] ++ r) (h-5) (c+11) := by
  simp [atLeft, Zipper.run, Zipper.step, table]
  omega

theorem settlement_ones (n : ℕ) (l : List Bool) :
    true :: (List.replicate n true ++ [true,false,true,true,true,true] ++ l) =
      List.replicate (n+2) true ++ [false,true,true,true,true] ++ l := by
  rw [show n+2=(n+1)+1 by omega, List.replicate_add]
  simp only [List.replicate_succ, List.cons_append]
  rw [List.append_assoc]
  simp [List.append_assoc]

theorem right_settlement (n : ℕ) (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run (4*n+32)
      ⟨some .C, true::l, [true,true,true,false,false] ++ List.replicate n true ++ [false,false,false] ++ r, h, c⟩ =
      atLeft l ([false,true,true,true,false,false] ++ List.replicate (n+3) true ++ r)
        (h-2) (c+4*n+32) := by
  have cost : 4*n+32 = ((11+n)+4)+3*(n+2)+11 := by omega
  rw [cost, Zipper.run_add (((11+n)+4)+3*(n+2)) 11,
    Zipper.run_add ((11+n)+4) (3*(n+2)), Zipper.run_add (11+n) 4,
    Zipper.run_add 11 n]
  simp only [List.append_assoc]
  rw [settlement_prefix, a1_strip]
  simp only [List.cons_append, List.nil_append]
  rw [settlement_z]
  have shape :
      (⟨some .E, List.replicate n true ++ ([true,false,true,true,true,true] ++ l),
        true::false::true::r, h+5+n, c+11+n+4⟩ : Zipper) =
      atLeft (List.replicate (n+2) true ++ ([false,true,true,true,true] ++ l))
        (false::true::r) (h+5+n) (c+11+n+4) := by
    have hs := settlement_ones n l
    simp only [List.append_assoc, List.cons_append, List.nil_append] at hs
    simp only [List.cons_append, List.nil_append]
    rw [← hs]
    rfl
  simp only [List.cons_append, List.nil_append] at shape
  rw [shape, q_boundary_strip]
  have tail := settlement_tail l (List.replicate (n+2) true ++ true::r) (h+5+n-(n+2)) (c+11+n+4+3*(n+2))
  simp only [List.cons_append, List.nil_append] at tail
  push_cast
  rw [tail]
  have ones : List.replicate (n+2) true ++ true::r = List.replicate (n+3) true ++ r := by
    conv_rhs => rw [show n+3=(n+2)+1 by omega, List.replicate_add]
    simp only [List.replicate_one, List.append_assoc, List.cons_append, List.nil_append]
  rw [ones]
  rw [show h+5+(n:ℤ)-((n:ℤ)+2)-5=h-2 by omega,
    show c+11+n+4+3*(n+2)+11=c+4*n+32 by omega]

theorem right_settlement_counter (b : ℕ) (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run (12*b+44)
      ⟨some .C, true::l, [true,true,true,false,false] ++ List.replicate (3*b+3) true ++ [false,false,false] ++ r, h, c⟩ =
      atLeft l ([false,true,true,true,false,false] ++ List.replicate (3*b+6) true ++ r)
        (h-2) (c+12*b+44) := by
  convert right_settlement (3*b+3) l r h c using 1 <;> congr 1 <;> omega


theorem right_settlement_counted (b : ℕ) (l r : List Bool) (h : ℤ) (c : ℕ) :
    CountedRun table (12*b+44)
      (Zipper.config ⟨some .C, true::l,
        [true,true,true,false,false] ++ List.replicate (3*b+3) true ++ [false,false,false] ++ r, h, c⟩)
      (atLeft l ([false,true,true,true,false,false] ++ List.replicate (3*b+6) true ++ r)
        (h-2) (c+12*b+44)).config := by
  apply CountedRun.of_active_endpoint
  · rw [← Zipper.run_config, right_settlement_counter]
  · simp [Zipper.config, atLeft]

end BeaverStructural.BB6
