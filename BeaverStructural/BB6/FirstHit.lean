import BeaverStructural.BB6.Stages
import BeaverStructural.BB6.Bridge

set_option compiler.extract_closed false
set_option maxHeartbeats 200000

namespace BeaverStructural.BB6

attribute [local irreducible] stage1 stage2 tower towerSum towerSquareSum
  towerWeightedSum bulkCost resetCost exhaustedWidth exhaustedRight

noncomputable def finalZipper : Zipper :=
  terminalZipper stage2.length (exhaustedWidth stage2) (exhaustedRight stage2)
    (29+stageHeadShift seed+stageHeadShift stage1+
      outerDisplacement stage2.count stage2.base)
    (27965+stageResetCost seed+stageResetCost stage1+bulkCost stage2.count stage2.base)

theorem three_stage_run (C0 C1 C2 : Counter)
    (h01 : C1=resetCounter C0) (h12 : C2=resetCounter C1)
    (hb0 : C0.count<2^C0.length) (hb1 : C1.count<2^C1.length)
    (hb2 : C2.count<2^C2.length)
    (hr0 : C0.count%3=1) (hr1 : C1.count%3=1) (hr2 : C2.count%3=2)
    (head : ℤ) (clock : ℕ) :
    CountedRun table
      ((stageResetCost C0+stageResetCost C1)+
        (bulkCost C2.count C2.base+haltCost C2.length (exhaustedWidth C2)))
      (stageEntry C0 head clock)
      (terminalZipper C2.length (exhaustedWidth C2) (exhaustedRight C2)
        (head+stageHeadShift C0+stageHeadShift C1+outerDisplacement C2.count C2.base)
        (clock+stageResetCost C0+stageResetCost C1+bulkCost C2.count C2.base)).config := by
  have h₀ := counted_stage_reset C0 hb0 hr0 head clock
  rw [← h01] at h₀
  have h₁ := counted_stage_reset C1 hb1 hr1 (head+stageHeadShift C0)
    (clock+stageResetCost C0)
  rw [← h12] at h₁
  have h₂ := counted_stage_terminal C2 hb2 hr2
    (head+stageHeadShift C0+stageHeadShift C1)
    (clock+stageResetCost C0+stageResetCost C1)
  exact (h₀.trans h₁).trans h₂

theorem three_stage_from_blank (C0 C1 C2 : Counter)
    (h01 : C1=resetCounter C0) (h12 : C2=resetCounter C1)
    (hb0 : C0.count<2^C0.length) (hb1 : C1.count<2^C1.length)
    (hb2 : C2.count<2^C2.length)
    (hr0 : C0.count%3=1) (hr1 : C1.count%3=1) (hr2 : C2.count%3=2)
    (hb : CountedRun table 27965 blank (stageEntry C0 29 27965)) :
    CountedRun table (clockFor C0 C1 C2) blank
      (terminalZipper C2.length (exhaustedWidth C2) (exhaustedRight C2)
        (29+stageHeadShift C0+stageHeadShift C1+outerDisplacement C2.count C2.base)
        (27965+stageResetCost C0+stageResetCost C1+bulkCost C2.count C2.base)).config := by
  have hs := three_stage_run C0 C1 C2 h01 h12 hb0 hb1 hb2 hr0 hr1 hr2 29 27965
  have ht := hb.trans hs
  simpa only [clockFor, stageResetCost, Nat.add_assoc] using ht

theorem terminalZipper_halted (L a b : ℕ) (h : ℤ) (c : ℕ) :
    (terminalZipper L a b h c).config.state = none := rfl

theorem zipper_config_clock (z : Zipper) : z.config.clock=z.clock := rfl

theorem terminal_word_of_eq (z : Zipper) (L a b : ℕ) (h : ℤ) (c : ℕ)
    (hz : z=terminalZipper L a b h c) :
    z.left.reverse++z.right=terminalPhysicalWord L a b := by
  rw [hz]
  exact terminal_full_word L a b h c

/-- Exact original blank-source execution, including every changed tape and the
final B1 write/right/halt tick. The clock is the explicit symbolic expression. -/
theorem blank_exact_run : CountedRun table exactN blank finalZipper.config := by
  rw [exactN_def]
  exact three_stage_from_blank seed stage1 stage2
    (by unfold stage1; rfl) (by unfold stage2; rfl)
    seed_count_bound stage1_count_bound stage2_count_bound
    seed_residue stage1_residue stage2_residue blank_to_seed

/-- Unconditional first-hit theorem for the original twelve-row blank machine. -/
theorem first_hit_exact : FirstHit table exactN blank :=
  blank_exact_run.firstHit (terminalZipper_halted _ _ _ _ _)

theorem exact_terminal_configuration :
    (step table)^[exactN] blank = finalZipper.config := blank_exact_run.reaches

theorem exact_terminal_clock : finalZipper.clock = exactN := by
  have ht := blank_exact_run.clock
  rw [zipper_config_clock, show blank.clock = 0 from rfl, Nat.zero_add] at ht
  exact ht

theorem terminal_word_source : finalZipper.left.reverse ++ finalZipper.right =
    terminalPhysicalWord stage2.length (exhaustedWidth stage2) (exhaustedRight stage2) :=
  terminal_word_of_eq finalZipper _ _ _ _ _ rfl

end BeaverStructural.BB6
