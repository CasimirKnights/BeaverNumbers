import BeaverStructural.Model

/-! The BB(3,4) machine `1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC` (Kropitz 2024): three states, four symbols, on a
two-way tape of symbols indexed by ℤ (A2 = 1RZ is the halting row); its executable zipper (left nearest cell first,
right beginning with the scanned cell, blank beyond both lists); blocks `blk s m` = s^m; the four sweeps of a block:
C leftward over 2s writing 3s, C rightward over 3s writing 2s, A rightward over 3s writing 2s, B rightward over 1s
writing 3s. -/

namespace BeaverStructural.BB34

inductive St | A | B | C
  deriving DecidableEq, Repr

inductive Sy | s0 | s1 | s2 | s3
  deriving DecidableEq, Repr

structure Row where
  write : Sy
  move : ℤ
  next : Option St

structure Config where
  state : Option St
  tape : ℤ → Sy
  head : ℤ
  clock : ℕ

def step (δ : St → Sy → Row) (c : Config) : Config :=
  match c.state with
  | none => c
  | some q =>
    { state := (δ q (c.tape c.head)).next
      tape := Function.update c.tape c.head (δ q (c.tape c.head)).write
      head := c.head + (δ q (c.tape c.head)).move
      clock := c.clock + 1 }

/-- The twelve rows; A2 is the halting row 1RZ. -/
def table : St → Sy → Row
  | .A, .s0 => ⟨.s1, 1, some .B⟩
  | .A, .s1 => ⟨.s3, -1, some .B⟩
  | .A, .s2 => ⟨.s1, 1, none⟩
  | .A, .s3 => ⟨.s2, 1, some .A⟩
  | .B, .s0 => ⟨.s2, -1, some .C⟩
  | .B, .s1 => ⟨.s3, 1, some .B⟩
  | .B, .s2 => ⟨.s1, -1, some .C⟩
  | .B, .s3 => ⟨.s2, 1, some .A⟩
  | .C, .s0 => ⟨.s3, 1, some .B⟩
  | .C, .s1 => ⟨.s1, -1, some .B⟩
  | .C, .s2 => ⟨.s3, -1, some .C⟩
  | .C, .s3 => ⟨.s2, 1, some .C⟩

def blank : Config := ⟨some .A, fun _ => .s0, 0, 0⟩

/-- Finite lists with blank rays: left nearest cell first, right beginning with the scanned cell. -/
def ray (l r : List Sy) : ℤ → Sy
  | .ofNat n => r[n]?.getD .s0
  | .negSucc n => l[n]?.getD .s0

@[simp] theorem ray_zero (l r : List Sy) : ray l r 0 = r.headD .s0 := by
  cases r <;> rfl

@[simp] theorem ray_right (l r : List Sy) (b : Sy) (p : ℤ) :
    ray (b :: l) r.tail (p - 1) = if p = 0 then b else ray l r p := by
  cases p with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      have hn : Int.ofNat (n + 1) ≠ 0 := by simp; omega
      rw [if_neg hn, show Int.ofNat (n + 1) - 1 = Int.ofNat n by simp]
      change r.tail[n]?.getD .s0 = r[n + 1]?.getD .s0
      simp
  | negSucc n =>
    have hp : Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega
    rw [hp]
    simp [ray]

@[simp] theorem ray_left (l r : List Sy) (b : Sy) (p : ℤ) :
    ray l.tail (l.headD .s0 :: b :: r.tail) (p + 1) = if p = 0 then b else ray l r p := by
  cases p with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      have hn : Int.ofNat (n + 1) ≠ 0 := by simp; omega
      rw [if_neg hn]
      change (l.headD .s0 :: b :: r.tail)[n + 2]?.getD .s0 = r[n + 1]?.getD .s0
      simp
  | negSucc n =>
    cases n with
    | zero =>
      change l.headD .s0 = l[0]?.getD .s0
      cases l <;> rfl
    | succ n =>
      have hp : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
      rw [hp]
      simp [ray, List.getElem?_tail]

structure Zip where
  state : Option St
  left : List Sy
  right : List Sy
  head : ℤ
  clock : ℕ
  deriving DecidableEq, Repr

def Zip.config (z : Zip) : Config :=
  ⟨z.state, fun p => ray z.left z.right (p - z.head), z.head, z.clock⟩

def Zip.step (z : Zip) : Zip :=
  match z.state with
  | none => z
  | some q =>
    let row := table q (z.right.headD .s0)
    if row.move = 1 then
      ⟨row.next, row.write :: z.left, z.right.tail, z.head + 1, z.clock + 1⟩
    else
      ⟨row.next, z.left.tail, z.left.headD .s0 :: row.write :: z.right.tail, z.head - 1, z.clock + 1⟩

theorem Zip.step_config (z : Zip) : z.step.config = BeaverStructural.BB34.step table z.config := by
  cases z with
  | mk q l r h c =>
    cases q with
    | none => rfl
    | some q =>
      have moves : (table q (r.headD .s0)).move = 1 ∨ (table q (r.headD .s0)).move = -1 := by
        cases q <;> cases r.headD Sy.s0 <;> simp [table]
      rcases moves with hm | hm
      · simp only [Zip.step, hm, ↓reduceIte, Zip.config, BeaverStructural.BB34.step, sub_self, ray_zero]
        congr 1
        funext p
        rw [show p - (h + 1) = (p - h) - 1 by omega, ray_right]
        by_cases hp : p = h
        · subst p; simp
        · simp [Function.update, hp, show p - h ≠ 0 by omega]
      · simp only [Zip.step, hm, show (-1 : ℤ) ≠ 1 by omega, ↓reduceIte, Zip.config,
          BeaverStructural.BB34.step, sub_self, ray_zero]
        congr 1
        · funext p
          rw [show p - (h - 1) = (p - h) + 1 by omega, ray_left]
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

theorem Zip.run_config (n : ℕ) (z : Zip) :
    (z.run n).config = (BeaverStructural.BB34.step table)^[n] z.config := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => rw [Zip.run, ih, Zip.step_config, Function.iterate_succ_apply]

theorem zip_eq {q q' : Option St} {l l' r r' : List Sy} {h h' : ℤ} {c c' : ℕ}
    (e₁ : q = q') (e₂ : l = l') (e₃ : r = r') (e₄ : h = h') (e₅ : c = c') :
    (⟨q, l, r, h, c⟩ : Zip) = ⟨q', l', r', h', c'⟩ := by
  subst e₁ e₂ e₃ e₄ e₅; rfl

theorem chain {z₁ z₂ z₃ : Zip} {a b : ℕ} (h₁ : z₁.run a = z₂) (h₂ : z₂.run b = z₃) : z₁.run (a + b) = z₃ := by
  rw [Zip.run_add, h₁, h₂]

/-- s^m. -/
def blk (s : Sy) : ℕ → List Sy
  | 0 => []
  | m + 1 => s :: blk s m

@[simp] theorem blk_zero (s : Sy) : blk s 0 = [] := rfl

@[simp] theorem blk_succ (s : Sy) (m : ℕ) : blk s (m + 1) = s :: blk s m := rfl

@[simp] theorem blk_append_cons (s : Sy) (m : ℕ) (X : List Sy) : blk s m ++ s :: X = s :: (blk s m ++ X) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [ih]

theorem blk_snoc (s : Sy) (m : ℕ) (X : List Sy) : blk s m ++ s :: X = blk s (m + 1) ++ X := by
  simp

theorem blk_add (s : Sy) (a b : ℕ) (X : List Sy) : blk s a ++ (blk s b ++ X) = blk s (a + b) ++ X := by
  induction a with
  | zero => simp
  | succ a ih => rw [show a + 1 + b = (a + b) + 1 by ring]; simp [ih]

theorem blk_count (s : Sy) (m : ℕ) : (blk s m).count s = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [ih]

theorem blk_count_ne (s t : Sy) (ht : s ≠ t) (m : ℕ) : (blk s m).count t = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [ih, ht]

/-- C rightward across 3^m, writing 2^m. -/
theorem crossC3 (m : ℕ) (L R : List Sy) (h : ℤ) (c : ℕ) :
    Zip.run m ⟨some .C, L, blk .s3 m ++ R, h, c⟩ = ⟨some .C, blk .s2 m ++ L, R, h + (m : ℤ), c + m⟩ := by
  induction m generalizing L h c with
  | zero => simp [Zip.run]
  | succ m ih =>
    rw [show m + 1 = 1 + m by ring, Zip.run_add]
    have s : Zip.run 1 ⟨some .C, L, blk .s3 (1 + m) ++ R, h, c⟩ =
        ⟨some .C, .s2 :: L, blk .s3 m ++ R, h + 1, c + 1⟩ := by
      rw [show 1 + m = m + 1 by ring]
      simp [Zip.run, Zip.step, table]
    rw [s, ih]
    exact zip_eq rfl (by rw [blk_snoc, show m + 1 = 1 + m by ring]) rfl (by push_cast; ring) (by ring)

/-- A rightward across 3^m, writing 2^m. -/
theorem crossA3 (m : ℕ) (L R : List Sy) (h : ℤ) (c : ℕ) :
    Zip.run m ⟨some .A, L, blk .s3 m ++ R, h, c⟩ = ⟨some .A, blk .s2 m ++ L, R, h + (m : ℤ), c + m⟩ := by
  induction m generalizing L h c with
  | zero => simp [Zip.run]
  | succ m ih =>
    rw [show m + 1 = 1 + m by ring, Zip.run_add]
    have s : Zip.run 1 ⟨some .A, L, blk .s3 (1 + m) ++ R, h, c⟩ =
        ⟨some .A, .s2 :: L, blk .s3 m ++ R, h + 1, c + 1⟩ := by
      rw [show 1 + m = m + 1 by ring]
      simp [Zip.run, Zip.step, table]
    rw [s, ih]
    exact zip_eq rfl (by rw [blk_snoc, show m + 1 = 1 + m by ring]) rfl (by push_cast; ring) (by ring)

/-- B rightward across 1^m, writing 3^m. -/
theorem crossB1 (m : ℕ) (L R : List Sy) (h : ℤ) (c : ℕ) :
    Zip.run m ⟨some .B, L, blk .s1 m ++ R, h, c⟩ = ⟨some .B, blk .s3 m ++ L, R, h + (m : ℤ), c + m⟩ := by
  induction m generalizing L h c with
  | zero => simp [Zip.run]
  | succ m ih =>
    rw [show m + 1 = 1 + m by ring, Zip.run_add]
    have s : Zip.run 1 ⟨some .B, L, blk .s1 (1 + m) ++ R, h, c⟩ =
        ⟨some .B, .s3 :: L, blk .s1 m ++ R, h + 1, c + 1⟩ := by
      rw [show 1 + m = m + 1 by ring]
      simp [Zip.run, Zip.step, table]
    rw [s, ih]
    exact zip_eq rfl (by rw [blk_snoc, show m + 1 = 1 + m by ring]) rfl (by push_cast; ring) (by ring)

/-- C leftward from a 2 across 2^m to the cell x beyond, writing 3^(m+1). -/
theorem crossC2 (m : ℕ) (x : Sy) (L R : List Sy) (h : ℤ) (c : ℕ) :
    Zip.run (m + 1) ⟨some .C, blk .s2 m ++ x :: L, .s2 :: R, h, c⟩ =
      ⟨some .C, L, x :: (blk .s3 (m + 1) ++ R), h - ((m : ℤ) + 1), c + (m + 1)⟩ := by
  induction m generalizing R h c with
  | zero => simp [Zip.run, Zip.step, table]
  | succ m ih =>
    have s : Zip.run 1 ⟨some .C, blk .s2 (m + 1) ++ x :: L, .s2 :: R, h, c⟩ =
        ⟨some .C, blk .s2 m ++ x :: L, .s2 :: .s3 :: R, h - 1, c + 1⟩ := by
      simp [Zip.run, Zip.step, table]
    have t := chain s (ih (.s3 :: R) (h - 1) (c + 1))
    refine (congrArg (fun k => Zip.run k _) (show m + 1 + 1 = 1 + (m + 1) by ring)).trans (t.trans ?_)
    exact zip_eq rfl rfl (by simp) (by push_cast; ring) (by ring)

/-- C leftward from a 2 across 2^m into the blank tape, writing 3^(m+1). -/
theorem crossC2z (m : ℕ) (R : List Sy) (h : ℤ) (c : ℕ) :
    Zip.run (m + 1) ⟨some .C, blk .s2 m, .s2 :: R, h, c⟩ =
      ⟨some .C, [], .s0 :: (blk .s3 (m + 1) ++ R), h - ((m : ℤ) + 1), c + (m + 1)⟩ := by
  induction m generalizing R h c with
  | zero => simp [Zip.run, Zip.step, table]
  | succ m ih =>
    have s : Zip.run 1 ⟨some .C, blk .s2 (m + 1), .s2 :: R, h, c⟩ =
        ⟨some .C, blk .s2 m, .s2 :: .s3 :: R, h - 1, c + 1⟩ := by
      simp [Zip.run, Zip.step, table]
    have t := chain s (ih (.s3 :: R) (h - 1) (c + 1))
    refine (congrArg (fun k => Zip.run k _) (show m + 1 + 1 = 1 + (m + 1) by ring)).trans (t.trans ?_)
    exact zip_eq rfl rfl (by simp) (by push_cast; ring) (by ring)

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.Zip.step_config
#print axioms BeaverStructural.BB34.crossC3
#print axioms BeaverStructural.BB34.crossA3
#print axioms BeaverStructural.BB34.crossB1
#print axioms BeaverStructural.BB34.crossC2
#print axioms BeaverStructural.BB34.crossC2z
