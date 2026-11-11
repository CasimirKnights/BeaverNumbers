import BeaverStructural.BB6.Machine
import BeaverStructural.Model

namespace BeaverStructural.BB6

/-- A counted original execution, including the exclusion of every earlier halt. -/
structure CountedRun {Q : Type} (δ : Q → Bool → Row Q) (n : ℕ)
    (c d : Config Q) : Prop where
  reaches : (step δ)^[n] c = d
  active : ∀ k < n, ¬ Stopped δ k c

variable {Q : Type} {δ : Q → Bool → Row Q} {c d e : Config Q} {n m : ℕ}

namespace CountedRun

theorem refl (c : Config Q) : CountedRun δ 0 c c := ⟨rfl, by simp⟩

theorem one (c : Config Q) (hc : c.state ≠ none) :
    CountedRun δ 1 c (step δ c) := by
  refine ⟨rfl, ?_⟩
  intro k hk
  have : k = 0 := by omega
  subst k
  exact hc

theorem trans (h₁ : CountedRun δ n c d) (h₂ : CountedRun δ m d e) :
    CountedRun δ (n + m) c e := by
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm n m, Function.iterate_add_apply, h₁.reaches, h₂.reaches]
  · intro k hk hs
    by_cases hkn : k < n
    · exact h₁.active k hkn hs
    · have hnk : n ≤ k := by omega
      have he : k = n + (k - n) := by omega
      have hr : (step δ)^[k] c = (step δ)^[k-n] d := by
        calc
          (step δ)^[k] c = (step δ)^[(k-n)+n] c := by congr 2; omega
          _ = (step δ)^[k-n] d := by rw [Function.iterate_add_apply, h₁.reaches]
      apply h₂.active (k - n) (by omega)
      simpa only [Stopped, hr] using hs

theorem clock (h : CountedRun δ n c d) : d.clock = c.clock + n := by
  rw [← h.reaches]
  exact iterate_clock δ c n h.active

theorem firstHit (h : CountedRun δ n c d) (hd : d.state = none) : FirstHit δ n c :=
  ⟨by simpa only [Stopped, h.reaches] using hd, h.active⟩

/-- A still-active exact endpoint proves that no previous transition halted. -/
theorem of_active_endpoint (h : (step δ)^[n] c = d) (hd : d.state ≠ none) :
    CountedRun δ n c d := by
  refine ⟨h, ?_⟩
  intro k hk hs
  apply hd
  have := stopped_mono δ c hs (Nat.le_of_lt hk)
  simpa only [Stopped, h] using this

/-- The physical clock cannot gain more than one per original instruction. -/
theorem clock_le (δ : Q → Bool → Row Q) (n : ℕ) (c : Config Q) :
    ((step δ)^[n] c).clock ≤ c.clock + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    cases hs : ((step δ)^[n] c).state with
    | none => rw [step_stopped δ _ hs]; omega
    | some q => rw [step_active_clock δ _ q hs]; omega

/-- Exact clock gain excludes padded iterations after a premature halt. -/
theorem of_clock_endpoint (h : (step δ)^[n] c = d)
    (hc : d.clock = c.clock + n) : CountedRun δ n c d := by
  refine ⟨h, ?_⟩
  intro k hk hs
  have hfix : ∀ j : ℕ, (step δ)^[j] ((step δ)^[k] c) = (step δ)^[k] c := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, step_stopped δ _ hs]
  have heq : d = (step δ)^[k] c := by
    rw [← h, show n = (n-k)+k by omega, Function.iterate_add_apply, hfix]
  have hb := clock_le δ k c
  rw [← heq, hc] at hb
  omega

end CountedRun
end BeaverStructural.BB6
