import BeaverStructural.BB6.Tape

/-! The BB(7) champion `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF` in the machine model of
`BeaverStructural.Correspondence` (E0 = 1RZ is the halting row), its executable zipper (left nearest cell first, right
beginning with the scanned cell), periodic words `pw a b m` = (a b)^m nearest cell first, and the three sweeps:
B/C leftward across (1 0)^m, G/F rightward across (1 0)^m, and the six-step A period rightward. -/

namespace BeaverStructural.BB7

inductive St | A | B | C | D | E | F | G
  deriving DecidableEq, Repr

/-- The fourteen rows; E0 is the halting row 1RZ. -/
def table : St → Bool → Row St
  | .A, false => ⟨true, 1, some .B⟩
  | .A, true  => ⟨false, 1, some .A⟩
  | .B, false => ⟨true, -1, some .C⟩
  | .B, true  => ⟨true, -1, some .F⟩
  | .C, false => ⟨true, 1, some .D⟩
  | .C, true  => ⟨false, -1, some .B⟩
  | .D, false => ⟨true, 1, some .A⟩
  | .D, true  => ⟨true, -1, some .E⟩
  | .E, false => ⟨true, 1, none⟩
  | .E, true  => ⟨false, -1, some .C⟩
  | .F, false => ⟨true, 1, some .G⟩
  | .F, true  => ⟨true, -1, some .D⟩
  | .G, false => ⟨false, 1, some .G⟩
  | .G, true  => ⟨false, 1, some .F⟩

def blank : Config St := ⟨some .A, fun _ => false, 0, 0⟩

theorem table_halts_iff (q : St) (b : Bool) : (table q b).next = none ↔ q = .E ∧ b = false := by
  cases q <;> cases b <;> simp [table]

structure Zip where
  state : Option St
  left : List Bool
  right : List Bool
  head : ℤ
  clock : ℕ
  deriving Repr

def Zip.config (z : Zip) : Config St :=
  ⟨z.state, fun p => BB6.rayTape z.left z.right (p - z.head), z.head, z.clock⟩

def Zip.step (z : Zip) : Zip :=
  match z.state with
  | none => z
  | some q =>
    let row := table q (z.right.headD false)
    if row.move = 1 then
      ⟨row.next, row.write :: z.left, z.right.tail, z.head + 1, z.clock + 1⟩
    else
      ⟨row.next, z.left.tail, z.left.headD false :: row.write :: z.right.tail, z.head - 1, z.clock + 1⟩

theorem Zip.step_config (z : Zip) : z.step.config = BeaverStructural.step table z.config := by
  cases z with
  | mk q l r h c =>
    cases q with
    | none => rfl
    | some q =>
      have moves : (table q (r.headD false)).move = 1 ∨ (table q (r.headD false)).move = -1 := by
        cases q <;> cases r.headD false <;> simp [table]
      rcases moves with hm | hm
      · simp only [Zip.step, hm, ↓reduceIte, Zip.config, BeaverStructural.step, sub_self, BB6.rayTape_zero]
        congr 1
        funext p
        rw [show p - (h + 1) = (p - h) - 1 by omega, BB6.rayTape_right]
        by_cases hp : p = h
        · subst p; simp
        · simp [Function.update, hp, show p - h ≠ 0 by omega]
      · simp only [Zip.step, hm, show (-1 : ℤ) ≠ 1 by omega, ↓reduceIte, Zip.config, BeaverStructural.step,
          sub_self, BB6.rayTape_zero]
        congr 1
        · funext p
          rw [show p - (h - 1) = (p - h) + 1 by omega, BB6.rayTape_left]
          by_cases hp : p = h
          · subst p; simp
          · simp [Function.update, hp, show p - h ≠ 0 by omega]

def Zip.run : ℕ → Zip → Zip
  | 0, z => z
  | n + 1, z => run n z.step

theorem Zip.run_add (n m : ℕ) (z : Zip) : z.run (n + m) = (z.run n).run m := by
  induction n generalizing z with
  | zero => simp [Zip.run]
  | succ n ih => simpa only [Nat.succ_add, Zip.run] using ih z.step

theorem Zip.run_config (n : ℕ) (z : Zip) : (z.run n).config = (BeaverStructural.step table)^[n] z.config := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => rw [Zip.run, ih, Zip.step_config, Function.iterate_succ_apply]

theorem zip_eq {q q' : Option St} {l l' r r' : List Bool} {h h' : ℤ} {c c' : ℕ}
    (e₁ : q = q') (e₂ : l = l') (e₃ : r = r') (e₄ : h = h') (e₅ : c = c') :
    (⟨q, l, r, h, c⟩ : Zip) = ⟨q', l', r', h', c'⟩ := by
  subst e₁ e₂ e₃ e₄ e₅; rfl

theorem chain {z₁ z₂ z₃ : Zip} {a b : ℕ} (h₁ : z₁.run a = z₂) (h₂ : z₂.run b = z₃) : z₁.run (a + b) = z₃ := by
  rw [Zip.run_add, h₁, h₂]

/-- (a b)^m, nearest cell first. -/
def pw (a b : Bool) : ℕ → List Bool
  | 0 => []
  | m + 1 => a :: b :: pw a b m

@[simp] theorem pw_zero (a b : Bool) : pw a b 0 = [] := rfl

@[simp] theorem pw_succ (a b : Bool) (m : ℕ) : pw a b (m + 1) = a :: b :: pw a b m := rfl

@[simp] theorem pw_append_pair (a b : Bool) (m : ℕ) (X : List Bool) :
    pw a b m ++ a :: b :: X = a :: b :: (pw a b m ++ X) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [ih]

theorem pw_snoc (a b : Bool) (m : ℕ) (X : List Bool) : pw a b m ++ a :: b :: X = pw a b (m + 1) ++ X := by
  simp

@[simp] theorem pw_append_cons (a b : Bool) (m : ℕ) (X : List Bool) :
    pw a b m ++ a :: X = a :: (pw b a m ++ X) := by
  induction m generalizing a b X with
  | zero => rfl
  | succ m ih => simp only [pw_succ, List.cons_append, ih]

/-- B/C leftward across (1 0)^m. -/
theorem sweepB (m : ℕ) (L R : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (2 * m) ⟨some .B, pw true false m ++ L, false :: R, h, c⟩ =
      ⟨some .B, L, false :: (pw false true m ++ R), h - 2 * (m : ℤ), c + 2 * m⟩ := by
  induction m generalizing R h c with
  | zero => simp [Zip.run]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 + 2 * m by ring, Zip.run_add]
    have s : Zip.run 2 ⟨some .B, pw true false (m + 1) ++ L, false :: R, h, c⟩ =
        ⟨some .B, pw true false m ++ L, false :: (false :: true :: R), h - 1 - 1, c + 1 + 1⟩ := by
      simp [Zip.run, Zip.step, table]
    rw [s, ih]
    simp only [Zip.mk.injEq, true_and, List.cons.injEq]
    refine ⟨by rw [pw_snoc], by push_cast; ring, by ring⟩

/-- G/F rightward across (1 0)^m. -/
theorem sweepG (m : ℕ) (L R : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (2 * m) ⟨some .G, L, pw true false m ++ R, h, c⟩ =
      ⟨some .G, pw true false m ++ L, R, h + 2 * (m : ℤ), c + 2 * m⟩ := by
  induction m generalizing L h c with
  | zero => simp [Zip.run]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 + 2 * m by ring, Zip.run_add]
    have s : Zip.run 2 ⟨some .G, L, pw true false (m + 1) ++ R, h, c⟩ =
        ⟨some .G, true :: false :: L, pw true false m ++ R, h + 1 + 1, c + 1 + 1⟩ := by
      simp [Zip.run, Zip.step, table]
    rw [s, ih]
    simp only [Zip.mk.injEq, true_and]
    refine ⟨by rw [pw_snoc], by push_cast; ring, by ring⟩

theorem pw_true_head (m : ℕ) (R : List Bool) : ∃ Y, pw true false m ++ true :: R = true :: Y := by
  cases m with
  | zero => exact ⟨R, rfl⟩
  | succ m => exact ⟨false :: (pw true false m ++ true :: R), rfl⟩

/-- The six-step A period rightward. -/
theorem sweepA (m : ℕ) (L R : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (6 * m) ⟨some .A, L, true :: (pw true false m ++ true :: R), h, c⟩ =
      ⟨some .A, pw true false m ++ L, true :: true :: R, h + 2 * (m : ℤ), c + 6 * m⟩ := by
  induction m generalizing L h c with
  | zero => simp [Zip.run]
  | succ m ih =>
    rw [show 6 * (m + 1) = 6 + 6 * m by ring, Zip.run_add]
    obtain ⟨Y, hY⟩ := pw_true_head m R
    have s : Zip.run 6 ⟨some .A, L, true :: (pw true false (m + 1) ++ true :: R), h, c⟩ =
        ⟨some .A, true :: false :: L, true :: (pw true false m ++ true :: R), h + 1 + 1 + 1 - 1 - 1 + 1,
          c + 1 + 1 + 1 + 1 + 1 + 1⟩ := by
      simp only [pw_succ, List.cons_append]
      rw [hY]
      simp [Zip.run, Zip.step, table]
    rw [s, ih]
    simp only [Zip.mk.injEq, true_and]
    refine ⟨by rw [pw_snoc], by push_cast; ring, by ring⟩

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.Zip.step_config
#print axioms BeaverStructural.BB7.sweepB
#print axioms BeaverStructural.BB7.sweepG
#print axioms BeaverStructural.BB7.sweepA
