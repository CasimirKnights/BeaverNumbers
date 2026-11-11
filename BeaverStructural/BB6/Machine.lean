import BeaverStructural.Model

namespace BeaverStructural.BB6

/-- The original active states, with the final halt represented by `none`. -/
inductive State | A | B | C | D | E | F
  deriving DecidableEq, Repr

open State

/-- Original twelve rows, including the explicit B1 write/right/halt instruction. -/
def table : State → Bool → Row State
  | .A, false => ⟨true, 1, some .B⟩
  | .A, true  => ⟨true, 1, some .A⟩
  | .B, false => ⟨true, 1, some .C⟩
  | .B, true  => ⟨true, 1, none⟩
  | .C, false => ⟨true, -1, some .D⟩
  | .C, true  => ⟨false, 1, some .F⟩
  | .D, false => ⟨true, 1, some .A⟩
  | .D, true  => ⟨false, -1, some .E⟩
  | .E, false => ⟨false, -1, some .D⟩
  | .E, true  => ⟨true, 1, some .C⟩
  | .F, false => ⟨true, 1, some .A⟩
  | .F, true  => ⟨false, 1, some .E⟩

def blank : Config State := ⟨some .A, fun _ => false, 0, 0⟩

@[simp] theorem table_halts_iff (q : State) (b : Bool) :
    (table q b).next = none ↔ q = .B ∧ b = true := by
  cases q <;> cases b <;> simp [table]

/-- The stopping instruction retains the final write, head movement and clock. -/
theorem final_instruction (t : ℤ → Bool) (h : ℤ) (n : ℕ) (hb : t h = true) :
    step table ⟨some .B, t, h, n⟩ =
      ⟨none, Function.update t h true, h + 1, n + 1⟩ := by
  simp [step, table, hb]

end BeaverStructural.BB6
