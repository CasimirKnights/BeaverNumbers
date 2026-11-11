import BeaverStructural.BB6.Execution

namespace BeaverStructural.BB6

/-- Finite lists with implicit zero rays. Left is nearest-cell first; right
includes the scanned cell. The interpretation is defined at every integer. -/
def rayTape (l r : List Bool) : ℤ → Bool
  | .ofNat n => r[n]?.getD false
  | .negSucc n => l[n]?.getD false

@[simp] theorem rayTape_zero (l r : List Bool) : rayTape l r 0 = r.headD false := by
  cases r <;> rfl

/-- Full executable zipper, with absolute head and physical instruction clock. -/
structure Zipper where
  state : Option State
  left : List Bool
  right : List Bool
  head : ℤ
  clock : ℕ
  deriving DecidableEq, Repr

def Zipper.config (z : Zipper) : Config State :=
  ⟨z.state, fun p => rayTape z.left z.right (p-z.head), z.head, z.clock⟩

def Zipper.step (z : Zipper) : Zipper :=
  match z.state with
  | none => z
  | some q =>
    let row := table q (z.right.headD false)
    if row.move = 1 then
      ⟨row.next, row.write :: z.left, z.right.tail, z.head+1, z.clock+1⟩
    else
      ⟨row.next, z.left.tail, z.left.headD false :: row.write :: z.right.tail,
       z.head-1, z.clock+1⟩

@[simp] theorem rayTape_right (l r : List Bool) (b : Bool) (p : ℤ) :
    rayTape (b::l) r.tail (p-1) = if p=0 then b else rayTape l r p := by
  cases p with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      have hn : Int.ofNat (n+1) ≠ 0 := by simp; omega
      rw [if_neg hn, show Int.ofNat (n+1)-1 = Int.ofNat n by simp]
      change r.tail[n]?.getD false = r[n+1]?.getD false
      simp
  | negSucc n =>
    have hp : Int.negSucc n - 1 = Int.negSucc (n+1) := by omega
    rw [hp]
    simp [rayTape]

@[simp] theorem rayTape_left (l r : List Bool) (b : Bool) (p : ℤ) :
    rayTape l.tail (l.headD false :: b :: r.tail) (p+1) =
      if p=0 then b else rayTape l r p := by
  cases p with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      have hn : Int.ofNat (n+1) ≠ 0 := by simp; omega
      rw [if_neg hn]
      change (l.headD false :: b :: r.tail)[n+2]?.getD false = r[n+1]?.getD false
      simp
  | negSucc n =>
    cases n with
    | zero =>
      change l.headD false = l[0]?.getD false
      cases l <;> rfl
    | succ n =>
      have hp : Int.negSucc (n+1) + 1 = Int.negSucc n := by omega
      rw [hp]
      simp [rayTape, List.getElem?_tail]

/-- Refinement to the existing original configuration semantics, including both
zero exteriors and the final halt's write and head movement. -/
theorem Zipper.step_config (z : Zipper) : z.step.config = BeaverStructural.step table z.config := by
  cases z with
  | mk q l r h c =>
    cases q with
    | none => rfl
    | some q =>
      have moves : (table q (r.headD false)).move = 1 ∨
          (table q (r.headD false)).move = -1 := by
        cases q <;> cases r.headD false <;> simp [table]
      rcases moves with hm | hm
      · simp only [Zipper.step, hm, ↓reduceIte, Zipper.config, BeaverStructural.step,
          sub_self, rayTape_zero]
        congr 1
        funext p
        rw [show p-(h+1) = (p-h)-1 by omega, rayTape_right]
        by_cases hp : p=h
        · subst p; simp
        · simp [Function.update, hp, show p-h ≠ 0 by omega]
      · simp only [Zipper.step, hm, show (-1:ℤ) ≠ 1 by omega, ↓reduceIte,
          Zipper.config, BeaverStructural.step, sub_self, rayTape_zero]
        congr 1
        · funext p
          rw [show p-(h-1) = (p-h)+1 by omega, rayTape_left]
          by_cases hp : p=h
          · subst p; simp
          · simp [Function.update, hp, show p-h ≠ 0 by omega]

/-- Primitive execution, chosen tail-recursive for closed bridge certificates. -/
def Zipper.run : ℕ → Zipper → Zipper
  | 0, z => z
  | n+1, z => run n z.step

theorem Zipper.run_add (n m : ℕ) (z : Zipper) :
    z.run (n+m) = (z.run n).run m := by
  induction n generalizing z with
  | zero => simp [Zipper.run]
  | succ n ih => simpa only [Nat.succ_add, Zipper.run] using ih z.step

theorem Zipper.run_config (n : ℕ) (z : Zipper) :
    (z.run n).config = (BeaverStructural.step table)^[n] z.config := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [Zipper.run, ih, Zipper.step_config, Function.iterate_succ_apply]

def blankZipper : Zipper := ⟨some .A, [], [], 0, 0⟩
@[simp] theorem blankZipper_config : blankZipper.config = blank := by
  unfold blankZipper Zipper.config blank
  congr 1
  funext p
  cases p <;> rfl

/-- Physical left-to-right binary counter encoding, most significant digit first. -/
def counterWord : ℕ → ℕ → List Bool
  | 0, _ => []
  | n+1, v => counterWord n (v/2) ++
      (if v%2=0 then [true,true,true] else [true,false,false])

def counterLeft (L v m a w : ℕ) : List Bool :=
  [true,true,true,false,true,true] ++ counterWord L v ++
  [true,false,false,true,false] ++ List.replicate m true ++ counterWord a w

def counterRight (b : ℕ) : List Bool :=
  [false,true,true,true,false,false] ++ List.replicate (3*(b+1)) true

def counterZipper (L v m a w b : ℕ) (head : ℤ) (clock : ℕ) : Zipper :=
  let ll := (counterLeft L v m a w).reverse
  ⟨some .E, ll.tail, ll.headD false :: counterRight b, head, clock⟩

def counterConfig (L v m a w b : ℕ) (head : ℤ) (clock : ℕ) : Config State :=
  (counterZipper L v m a w b head clock).config

@[simp] theorem counterWord_length (L v : ℕ) : (counterWord L v).length = 3*L := by
  induction L generalizing v with
  | zero => rfl
  | succ L ih =>
    simp only [counterWord, List.length_append, ih]
    split <;> simp <;> omega

@[simp] theorem counterLeft_length (L v m a w : ℕ) :
    (counterLeft L v m a w).length = 11+3*L+m+3*a := by
  simp [counterLeft]; omega

end BeaverStructural.BB6
