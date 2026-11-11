import BeaverStructural.BB7b.High
import BeaverStructural.BB7b.RuleE
import BeaverStructural.BB7b.EntryData

/-! The BB(7) machine of October 2026 from the blank tape: K(8; 0, 1^19) at step 3959, the ladder
K(Acc_i; 0^(i+1), 1, 1^(18−i)) → K(Acc_(i+1); 0^(i+2), 1^(18−i)) by the high-level rule with n = 1, the halt from
K(Acc_19; 0^20) by rule E; the first stop is exactly at τ, and the halted tape holds σ ones. -/

namespace BeaverStructural.BB7b

open Finset

def blankZip : Zip := ⟨some .A, [], [], 0, 0⟩

theorem blankZip_config : blankZip.config = blank := by
  simp only [Zip.config, blankZip, blank]
  congr 1
  funext p
  generalize p - 0 = x
  cases x <;> rfl

theorem getD_append_false (r : List Bool) : ∀ n : ℕ, (r ++ [false])[n]?.getD false = r[n]?.getD false := by
  induction r with
  | nil => intro n; cases n <;> simp
  | cons b r ih =>
    intro n
    cases n with
    | zero => simp
    | succ n => simpa using ih n

theorem config_right_false (q : Option St) (l r : List Bool) (h : ℤ) (c : ℕ) :
    (⟨q, l, r ++ [false], h, c⟩ : Zip).config = (⟨q, l, r, h, c⟩ : Zip).config := by
  simp only [Zip.config]
  congr 1
  funext p
  generalize p - h = x
  cases x with
  | ofNat n => exact getD_append_false r n
  | negSucc n => rfl

theorem config_right_false3 (q : Option St) (l r : List Bool) (h : ℤ) (c : ℕ) :
    (⟨q, l, r ++ List.replicate 3 false, h, c⟩ : Zip).config = (⟨q, l, r, h, c⟩ : Zip).config := by
  rw [show r ++ List.replicate 3 false = ((r ++ [false]) ++ [false]) ++ [false] by simp [List.replicate],
    config_right_false, config_right_false, config_right_false]

theorem run_config_congr {z z' : Zip} (e : z.config = z'.config) (t : ℕ) :
    (Zip.run t z).config = (Zip.run t z').config := by
  rw [Zip.run_config, Zip.run_config, e]

/-- The blank-tape run at step 3959 is K(8; 0, 1^19). -/
theorem entry_config : (Zip.run 3959 blankZip).config =
    (kc (0 :: List.replicate 19 1) 8 0 (-55) 3959).config := by
  rw [blankZip, entry_run]
  obtain ⟨hl, hr⟩ := entry_lists
  cases e : entryZip with
  | mk q l r h c =>
    rw [e] at hl hr
    simp only at hl hr
    have hq : q = some .E := by have := congrArg Zip.state e; simpa [entryZip] using this.symm
    have hh : h = -55 := by have := congrArg Zip.head e; simpa [entryZip] using this.symm
    have hc : c = 3959 := by have := congrArg Zip.clock e; simpa [entryZip] using this.symm
    subst hq hh hc
    simp only [List.replicate_zero] at hl
    rw [hl, hr]
    exact config_right_false3 _ _ _ _ _

/-- The ladder through the first J positions. -/
theorem ladder (J : ℕ) (hJ : J ≤ 19) : ∃ h' : ℤ,
    Zip.run (∑ i ∈ range J, T (i + 1) 1 (Acc i)) (kc (0 :: List.replicate 19 1) 8 0 (-55) 3959) =
      kc (List.replicate (J + 1) 0 ++ List.replicate (19 - J) 1) (Acc J) 0 h'
        (3959 + ∑ i ∈ range J, T (i + 1) 1 (Acc i)) := by
  induction J with
  | zero => exact ⟨-55, by simp [Zip.run, Acc]⟩
  | succ J ih =>
    obtain ⟨h1, e1⟩ := ih (by omega)
    have hrep : List.replicate (19 - J) 1 = 1 :: List.replicate (18 - J) 1 := by
      rw [show 19 - J = (18 - J) + 1 by omega, List.replicate_succ]
    rw [hrep] at e1
    obtain ⟨h2, e2⟩ := (high (J + 1) (by omega)).1 1 (Acc J) (List.replicate (18 - J) 1) h1
      (3959 + ∑ i ∈ range J, T (i + 1) 1 (Acc i)) (by have := Acc_ge J; omega)
    refine ⟨h2, ?_⟩
    rw [sum_range_succ, Zip.run_add, e1, e2]
    have hl : List.replicate (J + 1) 0 ++ 0 :: List.replicate (18 - J) 1 =
        List.replicate (J + 1 + 1) 0 ++ List.replicate (19 - (J + 1)) 1 := by
      rw [show 19 - (J + 1) = 18 - J by omega, replicate_succ_append (J + 1) 0 (List.replicate (18 - J) 1)]
    rw [hl]
    exact zip_eq rfl rfl rfl rfl (by ring)

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

/-- From the entry: a ladder of S steps to K(m + 7; 0^20), then rule E. -/
theorem run_gen (S m : ℕ) (h1 : ℤ)
    (e1 : Zip.run S (kc (0 :: List.replicate 19 1) 8 0 (-55) 3959) =
      kc [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (m + 7) 0 h1 (3959 + S)) :
    ∃ hd : ℤ, (Zip.run (3959 + (S + costE m)) blankZip).config =
      (halted m hd (3959 + (S + costE m))).config := by
  obtain ⟨hd, e2⟩ := rule_E m h1 (3959 + S)
  refine ⟨hd, ?_⟩
  rw [Zip.run_add, run_config_congr entry_config, Zip.run_add, e1, e2]
  exact congrArg Zip.config (zip_eq rfl rfl rfl rfl (by ring))

/-- The blank-tape run at step τ is the halted configuration of rule E at a = Acc 19, with clock τ. -/
theorem run_tau : ∃ (m : ℕ) (hd : ℤ), Acc 19 = m + 7 ∧
    (Zip.run tau blankZip).config = (halted m hd tau).config := by
  obtain ⟨m, hm⟩ : ∃ m, Acc 19 = m + 7 := ⟨Acc 19 - 7, by have := Acc_ge 19; omega⟩
  obtain ⟨h1, e1⟩ := ladder 19 le_rfl
  have hz : List.replicate (19 + 1) 0 ++ List.replicate (19 - 19) 1 =
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by decide
  rw [hz, hm] at e1
  obtain ⟨hd, e⟩ := run_gen _ m h1 e1
  refine ⟨m, hd, hm, ?_⟩
  have ht : tau = 3959 + (∑ i ∈ range 19, T (i + 1) 1 (Acc i) + costE m) := by
    rw [tau_tauF, tauF_eq, hm, Nat.add_sub_cancel]
    exact Nat.add_assoc _ _ _
  rw [ht]
  exact e

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

theorem fields_of_config {z z' : Zip} (e : z.config = z'.config) : z.state = z'.state ∧ z.clock = z'.clock :=
  ⟨congrArg Config.state e, congrArg Config.clock e⟩

theorem halted_state (m : ℕ) (h : ℤ) (c : ℕ) : (halted m h c).state = none := rfl

theorem halted_clock (m : ℕ) (h : ℤ) (c : ℕ) : (halted m h c).clock = c := rfl

/-- The run from the blank tape is halted at step τ with clock τ. -/
theorem machine_halted : (Zip.run tau blankZip).state = none ∧ (Zip.run tau blankZip).clock = tau := by
  obtain ⟨m, hd, _, e⟩ := run_tau
  have h := fields_of_config e
  exact ⟨h.1.trans (halted_state m hd tau), h.2.trans (halted_clock m hd tau)⟩

/-- The machine halts at step τ and at no earlier step. -/
theorem machine_first_stop :
    ((BeaverStructural.step table)^[tau] blank).state = none ∧
      ∀ t < tau, ((BeaverStructural.step table)^[t] blank).state ≠ none :=
  first_stop_of machine_halted.1 machine_halted.2

/-- The halted tape is that of a zipper whose two sides hold exactly σ ones. -/
theorem machine_sigma : ∃ z : Zip, ((BeaverStructural.step table)^[tau] blank) = z.config ∧
    z.left.count true + z.right.count true = sigma := by
  obtain ⟨m, hd, hm, e⟩ := run_tau
  refine ⟨halted m hd tau, ?_, ?_⟩
  · rw [← blankZip_config, ← Zip.run_config]; exact e
  · rw [halted_ones, sigma_sigF, sigF_eq, hm]

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.machine_first_stop
#print axioms BeaverStructural.BB7b.machine_sigma
