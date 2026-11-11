import BeaverStructural.BB6.Outer
import BeaverStructural.BB6.Reset

namespace BeaverStructural.BB6

def stageEntry (C : Counter) (head : ℤ) (clock : ℕ) : Config State :=
  counterConfig C.length C.count 2 C.base 0 (2^C.base-1) head clock

def stageResetCost (C : Counter) : ℕ :=
  bulkCost C.count C.base + resetCost C.length (exhaustedWidth C) (exhaustedRight C)

def stageHeadShift (C : Counter) : ℤ :=
  outerDisplacement C.count C.base + 3*(exhaustedRight C : ℤ)+5

theorem reset_count_same (L a : ℕ) :
    2^(L+a+2)-2^a-1 = (2^(L+2)-1)*2^a-1 := by
  rw [Nat.sub_mul, one_mul, ← pow_add]
  rw [show L+2+a=L+a+2 by omega]

/-- The actual source exhausts the complete counter, rebuilds its changed tape,
and enters the next counter. Residue one is proved for the actual two resets. -/
theorem counted_stage_reset (C : Counter) (hc : C.count < 2^C.length)
    (hr : C.count%3=1) (head : ℤ) (clock : ℕ) :
    CountedRun table (stageResetCost C) (stageEntry C head clock)
      (stageEntry (resetCounter C) (head+stageHeadShift C) (clock+stageResetCost C)) := by
  have h₁ := counter_outer_all C.length C.count C.base hc head clock
  rw [phaseMode_of_one _ hr, ← exhaustedWidth_eq_phaseWidth C (Or.inl hr)] at h₁
  change CountedRun table (bulkCost C.count C.base) (stageEntry C head clock)
    (counterConfig C.length 0 1 (exhaustedWidth C) 0 (exhaustedRight C)
      (head+outerDisplacement C.count C.base) (clock+bulkCost C.count C.base)) at h₁
  have h₂ := zero_outer_reset C.length (exhaustedWidth C) (exhaustedRight C)
    (head+outerDisplacement C.count C.base) (clock+bulkCost C.count C.base)
  have ht := h₁.trans h₂
  rw [reset_count_same] at ht
  simpa only [stageResetCost, stageEntry, stageHeadShift, resetCounter_length,
    resetCounter_count, resetCounter_base, add_assoc] using ht

theorem counted_stage_terminal (C : Counter) (hc : C.count < 2^C.length)
    (hr : C.count%3=2) (head : ℤ) (clock : ℕ) :
    CountedRun table (bulkCost C.count C.base + haltCost C.length (exhaustedWidth C))
      (stageEntry C head clock)
      (terminalZipper C.length (exhaustedWidth C) (exhaustedRight C)
        (head+outerDisplacement C.count C.base) (clock+bulkCost C.count C.base)).config := by
  have h₁ := counter_outer_all C.length C.count C.base hc head clock
  rw [phaseMode_of_two _ hr, ← exhaustedWidth_eq_phaseWidth C (Or.inr hr)] at h₁
  have h₂ := counter_terminal C.length (exhaustedWidth C) (exhaustedRight C)
    (head+outerDisplacement C.count C.base) (clock+bulkCost C.count C.base)
  exact h₁.trans h₂

end BeaverStructural.BB6
