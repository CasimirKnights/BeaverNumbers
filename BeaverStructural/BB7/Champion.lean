import BeaverStructural.BB7.High
import BeaverStructural.BB7.EntryData
import BeaverStructural.BB7.Digits
import Mathlib.Data.Set.Card

/-! The BB(7) champion from the blank tape: B(4; [1]*12) at step 8574, the ladder
B(A_j; [0]*j, 1, [1]*(11−j)) → B(A_(j+1); [0]*(j+1), [1]*(11−j)) by the high-level rule with n = 1, the halt from
B(A₁₂; [0]*12) in CH(A₁₂, 12) steps; the first stop is exactly at τ = 8574 + Σ_(j<12) T_j(1, A_j) + CH(A₁₂, 12), and
the halted tape has exactly σ = 3·A₁₂ + 34 cells holding 1. -/

namespace BeaverStructural.BB7

open Finset

def blankZip : Zip := ⟨some .A, [], [], 0, 0⟩

theorem blankZip_config : blankZip.config = blank := by
  simp only [Zip.config, blankZip, blank]
  congr 1
  funext p
  generalize p - 0 = x
  cases x <;> rfl

theorem entry : Zip.run 8574 blankZip = bZip 4 (List.replicate 12 1) 108 8574 := by
  rw [blankZip, entry_run]
  obtain ⟨hl, hr⟩ := entry_lists
  unfold bZip
  cases e : entryZip with
  | mk q l r h c =>
    rw [e] at hl hr
    simp only at hl hr
    have hq : q = some .A := by have := congrArg Zip.state e; simpa [entryZip] using this.symm
    have hh : h = 108 := by have := congrArg Zip.head e; simpa [entryZip] using this.symm
    have hc : c = 8574 := by have := congrArg Zip.clock e; simpa [entryZip] using this.symm
    subst hq hh hc
    simp only [List.replicate_zero, List.append_nil] at hl hr
    rw [hl, hr]

/-- The ladder through the first J levels. -/
theorem ladder (J : ℕ) (hJ : J ≤ 12) : ∃ h' : ℤ,
    Zip.run (∑ j ∈ range J, T j 1 (A j)) (bZip 4 (List.replicate 12 1) 108 8574) =
      bZip (A J) (List.replicate J 0 ++ List.replicate (12 - J) 1) h' (8574 + ∑ j ∈ range J, T j 1 (A j)) := by
  induction J with
  | zero => exact ⟨108, by simp [Zip.run, A]⟩
  | succ J ih =>
    obtain ⟨h1, e1⟩ := ih (by omega)
    have hrep : List.replicate (12 - J) 1 = 1 :: List.replicate (11 - J) 1 := by
      rw [show 12 - J = (11 - J) + 1 by omega, List.replicate_succ]
    rw [hrep] at e1
    obtain ⟨h2, e2⟩ := high J (by omega) 1 (A J) (List.replicate (11 - J) 1) h1 (8574 + ∑ j ∈ range J, T j 1 (A j))
    refine ⟨h2, ?_⟩
    rw [sum_range_succ, Zip.run_add, e1, e2]
    have hl : List.replicate J 0 ++ 0 :: List.replicate (11 - J) 1 =
        List.replicate (J + 1) 0 ++ List.replicate (12 - (J + 1)) 1 := by
      rw [replicate_succ_append, show 12 - (J + 1) = 11 - J by omega]
    rw [hl]
    exact zip_eq rfl rfl rfl rfl (by ring)

theorem ladder_top : ∃ h' : ℤ,
    Zip.run (8574 + ∑ j ∈ range 12, T j 1 (A j)) blankZip =
      bZip (A 12) (List.replicate 12 0) h' (8574 + ∑ j ∈ range 12, T j 1 (A j)) := by
  obtain ⟨h', e⟩ := ladder 12 le_rfl
  refine ⟨h', ?_⟩
  rw [Zip.run_add, entry, e]
  simp

theorem getD_append_false (r : List Bool) : ∀ n : ℕ, (r ++ [false])[n]?.getD false = r[n]?.getD false := by
  induction r with
  | nil => intro n; cases n <;> simp
  | cons b r ih =>
    intro n
    cases n with
    | zero => simp
    | succ n => simpa using ih n

theorem config_left_false (q : Option St) (l r : List Bool) (h : ℤ) (c : ℕ) :
    (⟨q, l ++ [false], r, h, c⟩ : Zip).config = (⟨q, l, r, h, c⟩ : Zip).config := by
  simp only [Zip.config]
  congr 1
  funext p
  generalize p - h = x
  cases x with
  | ofNat n => rfl
  | negSucc n => exact getD_append_false l n

theorem run_config_congr {z z' : Zip} (e : z.config = z'.config) (t : ℕ) :
    (Zip.run t z).config = (Zip.run t z').config := by
  rw [Zip.run_config, Zip.run_config, e]

/-- The left side of R4_12. -/
def r4Left (n : ℕ) (L : List Bool) : List Bool :=
  false :: (false :: (true :: (true :: (true :: (false :: (false :: (pw true false (n) ++ (true :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (true :: (false :: L))))))))))))))))))))))))))))))))))))))))))))))))

/-- The halted right side of R4_12. -/
def r4Right (n : ℕ) : List Bool :=
  true :: (true :: (pw true false (n + 2) ++ (false :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: (true :: (false :: (true :: [])))))))))))))))))))))))))))))))))))))))))))))

/-- The halted configuration of R4_12 from B(a; [0]*12). -/
def haltZip (a : ℕ) (h : ℤ) (c : ℕ) : Zip :=
  ⟨none, [true], r4Right (3 * a + 1), h + (-2 * ((3 * a + 1 : ℕ) : ℤ) + -47), c + (98 * (3 * a + 1) + 279)⟩

theorem rule_R4_12' (n : ℕ) (L : List Bool) (h : ℤ) (c : ℕ) :
    Zip.run (98 * n + 279) ⟨some .A, r4Left n L, [], h, c⟩ =
      ⟨none, true :: L, r4Right n, h + (-2 * (n : ℤ) + -47), c + (98 * n + 279)⟩ := rule_R4_12 n L h c

theorem bLeft_zeros12 (a : ℕ) : bLeft a (List.replicate 12 0) ++ [false] = r4Left (3 * a + 1) [] := by
  simp [bLeft, blk, r4Left, List.replicate_succ]

theorem halt_from (a : ℕ) (h : ℤ) (c : ℕ) :
    (Zip.run (CH a 12) (bZip a (List.replicate 12 0) h c)).config = (haltZip a h c).config := by
  rw [show CH a 12 = 98 * (3 * a + 1) + 279 by unfold CH; ring]
  have e1 : (bZip a (List.replicate 12 0) h c).config = (⟨some .A, r4Left (3 * a + 1) [], [], h, c⟩ : Zip).config := by
    rw [← bLeft_zeros12, config_left_false]; rfl
  rw [run_config_congr e1, rule_R4_12']
  rfl

theorem run_halted {z : Zip} (hz : z.state = none) (t : ℕ) : Zip.run t z = z := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Zip.run]
    have : z.step = z := by simp [Zip.step, hz]
    rw [this, ih]

theorem clock_le (t : ℕ) : ∀ z : Zip, (Zip.run t z).clock ≤ z.clock + t := by
  induction t with
  | zero => intro z; simp [Zip.run]
  | succ t ih =>
    intro z
    rw [Zip.run]
    have hs : z.step.clock ≤ z.clock + 1 := by
      rcases z with ⟨q, l, r, h, c⟩
      cases q with
      | none => simp [Zip.step]
      | some q =>
        simp only [Zip.step]
        split <;> simp
    have := ih z.step
    omega

/-- From B(a; [0]*12) reached at step S of the blank-tape run, the run is halted at step S + CH(a, 12), clock S + CH(a, 12). -/
theorem halts_after {S a : ℕ} {h' : ℤ} (e : Zip.run S blankZip = bZip a (List.replicate 12 0) h' S) :
    (Zip.run (S + CH a 12) blankZip).state = none ∧ (Zip.run (S + CH a 12) blankZip).clock = S + CH a 12 := by
  have hcfg : (Zip.run (S + CH a 12) blankZip).config = (haltZip a h' S).config := by
    rw [Zip.run_add, e]; exact halt_from _ _ _
  have hs := congrArg Config.state hcfg
  have hc := congrArg Config.clock hcfg
  simp only [Zip.config, haltZip] at hs hc
  refine ⟨hs, ?_⟩
  rw [hc]; unfold CH; ring

/-- A blank-tape run halted at N with clock N stops first at N. -/
theorem first_stop_of {N : ℕ} (hs : (Zip.run N blankZip).state = none) (hc : (Zip.run N blankZip).clock = N) :
    ((BeaverStructural.step table)^[N] blank).state = none ∧
      ∀ t < N, ((BeaverStructural.step table)^[t] blank).state ≠ none := by
  constructor
  · rw [← blankZip_config, ← Zip.run_config]; exact hs
  · intro t ht hnone
    rw [← blankZip_config, ← Zip.run_config] at hnone
    have h1 : Zip.run N blankZip = Zip.run t blankZip := by
      obtain ⟨d, rfl⟩ : ∃ d, N = t + d := ⟨N - t, by omega⟩
      rw [Zip.run_add, run_halted hnone]
    have h2 := clock_le t blankZip
    rw [h1] at hc
    have h3 : blankZip.clock = 0 := rfl
    omega

theorem tauF_body (Af : ℕ → ℕ) : tauF Af = (8574 + ∑ j ∈ range 12, T j 1 (Af j)) + CH (Af 12) 12 := rfl

/-- The champion's run from the blank tape is halted at step τ with clock τ. -/
theorem champion_halted : (Zip.run tau blankZip).state = none ∧ (Zip.run tau blankZip).clock = tau := by
  obtain ⟨h', e⟩ := ladder_top
  rw [tau_tauF, tauF_body]
  exact halts_after e

/-- The machine halts at step τ and at no earlier step. -/
theorem champion_first_stop :
    ((BeaverStructural.step table)^[tau] blank).state = none ∧
      ∀ t < tau, ((BeaverStructural.step table)^[t] blank).state ≠ none :=
  first_stop_of champion_halted.1 champion_halted.2

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.entry
#print axioms BeaverStructural.BB7.ladder_top
#print axioms BeaverStructural.BB7.halts_after
#print axioms BeaverStructural.BB7.first_stop_of
#print axioms BeaverStructural.BB7.champion_halted
#print axioms BeaverStructural.BB7.champion_first_stop
