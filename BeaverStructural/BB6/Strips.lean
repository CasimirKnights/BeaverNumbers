import BeaverStructural.BB6.Tape

/-! Arbitrary-length original-row strips. Every theorem retains arbitrary
left/right exterior lists and hence the complete interpreted integer tape. -/
namespace BeaverStructural.BB6

def atLeft (l r : List Bool) (h : ℤ) (c : ℕ) : Zipper :=
  ⟨some .E, l.tail, l.headD false :: r, h, c⟩

theorem q_boundary_once (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run 3 (atLeft (true::l) (false::r) h c) =
      atLeft l (false::true::r) (h-1) (c+3) := by
  simp [atLeft, Zipper.run, Zipper.step, table]

theorem replicate_append_cons (n : ℕ) (b : Bool) (r : List Bool) :
    List.replicate n b ++ b::r = b::(List.replicate n b ++ r) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem q_boundary_strip (n : ℕ) (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run (3*n) (atLeft (List.replicate n true ++ l) (false::r) h c) =
      atLeft l (false::(List.replicate n true ++ r)) (h-n) (c+3*n) := by
  induction n generalizing l r h c with
  | zero => simp [Zipper.run]
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega, Zipper.run_add]
    simp only [List.replicate_succ, List.cons_append]
    rw [q_boundary_once, ih, replicate_append_cons]
    congr 1 <;> push_cast <;> omega

theorem q_once (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run 3 ⟨some .E, true::l, true::false::r, h, c⟩ =
      ⟨some .E, l, true::false::true::r, h-1, c+3⟩ := by
  simp [Zipper.run, Zipper.step, table]

theorem q_strip (n : ℕ) (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run (3*n) ⟨some .E, List.replicate n true ++ l, true::false::r, h, c⟩ =
      ⟨some .E, l, true::false::(List.replicate n true ++ r), h-n, c+3*n⟩ := by
  induction n generalizing l r h c with
  | zero => simp [Zipper.run]
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega, Zipper.run_add]
    simp only [List.replicate_succ, List.cons_append]
    rw [q_once, ih]
    congr 1
    · rw [replicate_append_cons]
    · push_cast; omega
    · omega

theorem j_once (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run 3 ⟨some .C, l, true::true::true::r, h, c⟩ =
      ⟨some .C, true::false::false::l, r, h+3, c+3⟩ := by
  simp [Zipper.run, Zipper.step, table]
  omega

def writtenJ (n : ℕ) : List Bool := (List.replicate n [true,false,false]).flatten

theorem writtenJ_succ (n : ℕ) : writtenJ (n+1) = [true,false,false] ++ writtenJ n := by
  simp [writtenJ, List.replicate_succ]

theorem writtenJ_append (n : ℕ) : writtenJ n ++ [true,false,false] = writtenJ (n+1) := by
  simp only [writtenJ, List.replicate_add, List.flatten_append, List.replicate_one,
    List.flatten_cons, List.flatten_nil, List.append_nil]

theorem j_strip (n : ℕ) (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run (3*n) ⟨some .C, l, List.replicate (3*n) true ++ r, h, c⟩ =
      ⟨some .C, writtenJ n ++ l, r, h+3*n, c+3*n⟩ := by
  induction n generalizing l r h c with
  | zero => simp [Zipper.run, writtenJ]
  | succ n ih =>
    rw [show 3*(n+1)=3+3*n by omega, Zipper.run_add]
    rw [List.replicate_add]
    simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
    rw [j_once, ih]
    congr 1
    · rw [show true::false::false::l = [true,false,false] ++ l by rfl,
        ← List.append_assoc, writtenJ_append]
    · push_cast; omega
    · omega

theorem a1_strip (n : ℕ) (l r : List Bool) (h : ℤ) (c : ℕ) :
    Zipper.run n ⟨some .A, l, List.replicate n true ++ r, h, c⟩ =
      ⟨some .A, List.replicate n true ++ l, r, h+n, c+n⟩ := by
  induction n generalizing l r h c with
  | zero => simp [Zipper.run]
  | succ n ih =>
    simp only [List.replicate_succ, List.cons_append, Zipper.run, Zipper.step,
      List.headD_cons, table, List.tail_cons, ↓reduceIte]
    rw [ih]
    congr 1
    · exact replicate_append_cons n true l
    · push_cast; omega
    · omega

theorem q_boundary_counted (n : ℕ) (l r : List Bool) (h : ℤ) (c : ℕ) :
    CountedRun table (3*n)
      (atLeft (List.replicate n true ++ l) (false::r) h c).config
      (atLeft l (false::(List.replicate n true ++ r)) (h-n) (c+3*n)).config := by
  apply CountedRun.of_active_endpoint
  · rw [← Zipper.run_config, q_boundary_strip]
  · simp [Zipper.config, atLeft]

theorem j_counted (n : ℕ) (l r : List Bool) (h : ℤ) (c : ℕ) :
    CountedRun table (3*n)
      (Zipper.config ⟨some .C, l, List.replicate (3*n) true ++ r, h, c⟩)
      (Zipper.config ⟨some .C, writtenJ n ++ l, r, h+3*n, c+3*n⟩) := by
  apply CountedRun.of_active_endpoint
  · rw [← Zipper.run_config, j_strip]
  · simp [Zipper.config]

theorem a1_counted (n : ℕ) (l r : List Bool) (h : ℤ) (c : ℕ) :
    CountedRun table n
      (Zipper.config ⟨some .A, l, List.replicate n true ++ r, h, c⟩)
      (Zipper.config ⟨some .A, List.replicate n true ++ l, r, h+n, c+n⟩) := by
  apply CountedRun.of_active_endpoint
  · rw [← Zipper.run_config, a1_strip]
  · simp [Zipper.config]

end BeaverStructural.BB6
