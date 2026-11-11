import BeaverStructural.BB6.Tape

/-! The BB(7) machine `1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB` (Ketchersid, October 2026) in the machine
model of `BeaverStructural.Model` (C1 = 1RZ is the halting row), its executable zipper (left nearest cell first, right
beginning with the scanned cell), blocks `ones m` = 1^m, and the three crossings of a block: B rightward, E leftward,
F leftward. -/

namespace BeaverStructural.BB7b

inductive St | A | B | C | D | E | F | G
  deriving DecidableEq, Repr

/-- The fourteen rows; C1 is the halting row 1RZ. -/
def table : St → Bool → Row St
  | .A, false => ⟨true, 1, some .B⟩
  | .A, true  => ⟨false, 1, some .G⟩
  | .B, false => ⟨true, 1, some .C⟩
  | .B, true  => ⟨true, 1, some .B⟩
  | .C, false => ⟨false, 1, some .D⟩
  | .C, true  => ⟨true, 1, none⟩
  | .D, false => ⟨false, -1, some .E⟩
  | .D, true  => ⟨false, -1, some .D⟩
  | .E, false => ⟨false, -1, some .F⟩
  | .E, true  => ⟨true, -1, some .E⟩
  | .F, false => ⟨true, 1, some .A⟩
  | .F, true  => ⟨true, -1, some .F⟩
  | .G, false => ⟨true, -1, some .C⟩
  | .G, true  => ⟨false, 1, some .B⟩

def blank : Config St := ⟨some .A, fun _ => false, 0, 0⟩

theorem table_halts_iff (q : St) (b : Bool) : (table q b).next = none ↔ q = .C ∧ b = true := by
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

/-- `chain` across two writings of the middle zipper. -/
theorem chainB {z₁ z₂ z₂' z₃ : Zip} {a b : ℕ} (h₁ : z₁.run a = z₂) (h₂ : z₂'.run b = z₃) (e : z₂ = z₂') :
    z₁.run (a + b) = z₃ := by
  subst e; exact chain h₁ h₂

/-- 1^m. -/
def ones : ℕ → List Bool
  | 0 => []
  | m + 1 => true :: ones m

@[simp] theorem ones_zero : ones 0 = [] := rfl

@[simp] theorem ones_succ (m : ℕ) : ones (m + 1) = true :: ones m := rfl

@[simp] theorem ones_append_cons (m : ℕ) (X : List Bool) : ones m ++ true :: X = true :: (ones m ++ X) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [ih]

theorem ones_snoc (m : ℕ) (X : List Bool) : ones m ++ true :: X = ones (m + 1) ++ X := by
  simp

theorem ones_add (a b : ℕ) (X : List Bool) : ones a ++ (ones b ++ X) = ones (a + b) ++ X := by
  induction a with
  | zero => simp
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 by ring]; simp [ih]

/-- B rightward across 1^m. -/
theorem crossB (m : ℕ) (L R : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run m ⟨some .B, L, ones m ++ R, h, c⟩ = ⟨some .B, ones m ++ L, R, h + (m : ℤ), c + m⟩ := by
  induction m generalizing L h c with
  | zero => simp [Zip.run]
  | succ m ih =>
    rw [show m + 1 = 1 + m by ring, Zip.run_add]
    have s : Zip.run 1 ⟨some .B, L, ones (1 + m) ++ R, h, c⟩ =
        ⟨some .B, true :: L, ones m ++ R, h + 1, c + 1⟩ := by
      rw [show 1 + m = m + 1 by ring]
      simp [Zip.run, Zip.step, table]
    rw [s, ih]
    simp only [Zip.mk.injEq, true_and]
    refine ⟨by rw [ones_snoc, show m + 1 = 1 + m by ring], by push_cast; ring, by ring⟩

/-- E leftward across 1^m, standing on a 1. -/
theorem crossE (m : ℕ) (L R : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run m ⟨some .E, ones m ++ L, true :: R, h, c⟩ = ⟨some .E, L, ones m ++ true :: R, h - (m : ℤ), c + m⟩ := by
  induction m generalizing R h c with
  | zero => simp [Zip.run]
  | succ m ih =>
    rw [show m + 1 = 1 + m by ring, Zip.run_add]
    have s : Zip.run 1 ⟨some .E, ones (1 + m) ++ L, true :: R, h, c⟩ =
        ⟨some .E, ones m ++ L, true :: true :: R, h - 1, c + 1⟩ := by
      rw [show 1 + m = m + 1 by ring]
      simp [Zip.run, Zip.step, table]
    rw [s, ih]
    simp only [Zip.mk.injEq, true_and]
    refine ⟨by rw [show 1 + m = m + 1 by ring]; simp, by push_cast; ring, by ring⟩

/-- F leftward across 1^m, standing on a 1. -/
theorem crossF (m : ℕ) (L R : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run m ⟨some .F, ones m ++ L, true :: R, h, c⟩ = ⟨some .F, L, ones m ++ true :: R, h - (m : ℤ), c + m⟩ := by
  induction m generalizing R h c with
  | zero => simp [Zip.run]
  | succ m ih =>
    rw [show m + 1 = 1 + m by ring, Zip.run_add]
    have s : Zip.run 1 ⟨some .F, ones (1 + m) ++ L, true :: R, h, c⟩ =
        ⟨some .F, ones m ++ L, true :: true :: R, h - 1, c + 1⟩ := by
      rw [show 1 + m = m + 1 by ring]
      simp [Zip.run, Zip.step, table]
    rw [s, ih]
    simp only [Zip.mk.injEq, true_and]
    refine ⟨by rw [show 1 + m = m + 1 by ring]; simp, by push_cast; ring, by ring⟩

/-- (0 1)^j, nearest cell first: the trail left by j forward passes. -/
def tr : ℕ → List Bool
  | 0 => []
  | j + 1 => false :: true :: tr j

@[simp] theorem tr_zero : tr 0 = [] := rfl

@[simp] theorem tr_succ (j : ℕ) : tr (j + 1) = false :: true :: tr j := rfl

@[simp] theorem tr_append_pair (j : ℕ) (X : List Bool) :
    tr j ++ false :: true :: X = false :: true :: (tr j ++ X) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [ih]

/-- (0 1 0 1)^i, nearest cell first: the trail read by i backward passes. -/
def q4 : ℕ → List Bool
  | 0 => []
  | i + 1 => false :: true :: false :: true :: q4 i

@[simp] theorem q4_zero : q4 0 = [] := rfl

@[simp] theorem q4_succ (i : ℕ) : q4 (i + 1) = false :: true :: false :: true :: q4 i := rfl

theorem tr_double (i : ℕ) (X : List Bool) : tr (2 * i) ++ X = q4 i ++ X := by
  induction i with
  | zero => rfl
  | succ i ih => rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring]; simp [ih]

/-- (1 1 0 0)^i: the digits 1 written by i backward passes. -/
def c4 : ℕ → List Bool
  | 0 => []
  | i + 1 => true :: true :: false :: false :: c4 i

@[simp] theorem c4_zero : c4 0 = [] := rfl

@[simp] theorem c4_succ (i : ℕ) : c4 (i + 1) = true :: true :: false :: false :: c4 i := rfl

@[simp] theorem c4_append_unit (i : ℕ) (X : List Bool) :
    c4 i ++ true :: true :: false :: false :: X = true :: true :: false :: false :: (c4 i ++ X) := by
  induction i with
  | zero => rfl
  | succ i ih => simp [ih]

/-- The digit list on the tape: each digit d is (11)^d 00, and the right boundary is one 1. -/
def rgt : List ℕ → List Bool
  | [] => [true]
  | d :: t => ones (2 * d) ++ false :: false :: rgt t

/-- The configuration with counter b, accumulator a and digits ds: state E on the first cell of
`0 1^(2b+1) 00 (11)^a 00 [(11)^d 00 for d in ds] 1`, blank to the left. K(a; ds) is `kc ds a 0`. -/
abbrev kc (ds : List ℕ) (a b : ℕ) (h : ℤ) (c : ℕ) : Zip :=
  ⟨some .E, [], false :: (ones (2 * b + 1) ++ false :: false :: (ones (2 * a) ++ false :: false :: rgt ds)), h, c⟩

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.Zip.step_config
#print axioms BeaverStructural.BB7b.crossB
#print axioms BeaverStructural.BB7b.crossE
#print axioms BeaverStructural.BB7b.crossF
