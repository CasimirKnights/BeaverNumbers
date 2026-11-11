import BeaverStructural.BB34.Rules
import BeaverStructural.BB34.EntryData

/-! The BB(3,4) machine from the blank tape: B(16, 3, 0) with right context 2 at step 241, the rule at k = 16 with
n = 3 in T_14(3, 0) steps, the halt by A2; the first stop is exactly at τ, and the halted tape holds σ nonblank
cells.  The run is proved over a variable step count and accumulator (`run_gen`) and read at T_14(3, 0) and
g_14^3(0). -/

namespace BeaverStructural.BB34

open BeaverStructural.BB7 (g)

def blankZip : Zip := ⟨some .A, [], [], 0, 0⟩

theorem blankZip_config : blankZip.config = blank := by
  simp only [Zip.config, blankZip, blank]
  congr 1
  funext p
  generalize p - 0 = x
  cases x <;> rfl

theorem haltStep (L : List Sy) (h : ℤ) (c : ℕ) :
    Zip.run 1 ⟨some .A, L, [.s2], h, c⟩ = ⟨none, .s1 :: L, [], h + 1, c + 1⟩ := by
  simp [Zip.run, Zip.step, table]

/-- The halted zipper 0^∞ 3^(a+1) 2^16 1 Z> 0^∞ with clock t. -/
def halted (a t : ℕ) (h : ℤ) : Zip := ⟨none, .s1 :: (blk .s2 (14 + 1 + 1) ++ blk .s3 (a + 1)), [], h, t⟩

theorem entry_blank :
    Zip.run 241 blankZip = ⟨some .A, blk .s2 (14 + 1 + 1) ++ blk .s3 (0 + 1), blk .s1 3 ++ [.s2], 11, 241⟩ :=
  entry_run.trans entry_eq

/-- From the entry: a run of Tn steps to accumulator a, then the halting row. -/
theorem run_gen (Tn a : ℕ) (h1 : ℤ)
    (e1 : Zip.run Tn ⟨some .A, blk .s2 (14 + 1 + 1) ++ blk .s3 (0 + 1), blk .s1 3 ++ [.s2], 11, 241⟩ =
      ⟨some .A, blk .s2 (14 + 1 + 1) ++ blk .s3 (a + 1), [.s2], h1, 241 + Tn⟩) :
    Zip.run (241 + Tn + 1) blankZip = halted a (241 + Tn + 1) (h1 + 1) :=
  chain (chain entry_blank e1) (haltStep _ _ _)

/-- The blank-tape run at step τ is the halted zipper at accumulator g_14^3(0). -/
theorem run_tau : ∃ hd : ℤ, Zip.run tau blankZip = halted ((g 14)^[3] 0) tau hd := by
  obtain ⟨h1, e1⟩ := high 14 3 0 [.s2] 11 241
  refine ⟨h1 + 1, ?_⟩
  rw [tau_tauF, tauF_eq]
  exact run_gen (T 14 3 0) ((g 14)^[3] 0) h1 e1

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

/-- A blank-tape run halted at N with clock N stops first at N. -/
theorem first_stop_of {N : ℕ} (hs : (Zip.run N blankZip).state = none) (hc : (Zip.run N blankZip).clock = N) :
    ((BeaverStructural.BB34.step table)^[N] blank).state = none ∧
      ∀ t < N, ((BeaverStructural.BB34.step table)^[t] blank).state ≠ none := by
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

theorem halted_state (a t : ℕ) (h : ℤ) : (halted a t h).state = none := rfl

theorem halted_clock (a t : ℕ) (h : ℤ) : (halted a t h).clock = t := rfl

/-- The machine halts at step τ and at no earlier step. -/
theorem machine_first_stop :
    ((BeaverStructural.BB34.step table)^[tau] blank).state = none ∧
      ∀ t < tau, ((BeaverStructural.BB34.step table)^[t] blank).state ≠ none := by
  obtain ⟨hd, e⟩ := run_tau
  exact first_stop_of (by rw [e, halted_state]) (by rw [e, halted_clock])

/-- The nonblank cells of a list. -/
def nb (l : List Sy) : ℕ := (l.filter (fun s => decide (s ≠ Sy.s0))).length

theorem nb_append (a b : List Sy) : nb (a ++ b) = nb a + nb b := by
  unfold nb; rw [List.filter_append, List.length_append]

theorem nb_cons (s : Sy) (hs : s ≠ Sy.s0) (l : List Sy) : nb (s :: l) = nb l + 1 := by
  unfold nb; simp [hs]

theorem nb_blk (s : Sy) (hs : s ≠ Sy.s0) (m : ℕ) : nb (blk s m) = m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [blk_succ, nb_cons s hs, ih]

theorem halted_nb (a t : ℕ) (h : ℤ) : nb (halted a t h).left + nb (halted a t h).right = a + 18 := by
  show nb (Sy.s1 :: (blk .s2 (14 + 1 + 1) ++ blk .s3 (a + 1))) + 0 = a + 18
  rw [nb_cons Sy.s1 (by decide), nb_append, nb_blk Sy.s2 (by decide), nb_blk Sy.s3 (by decide)]
  omega

/-- The halted tape is that of a zipper whose two sides hold exactly σ nonblank cells. -/
theorem machine_sigma : ∃ z : Zip, ((BeaverStructural.BB34.step table)^[tau] blank) = z.config ∧
    nb z.left + nb z.right = sigma := by
  obtain ⟨hd, e⟩ := run_tau
  refine ⟨halted ((g 14)^[3] 0) tau hd, ?_, ?_⟩
  · rw [← blankZip_config, ← Zip.run_config, e]
  · rw [sigma_sigF, sigF_eq]
    exact halted_nb _ _ _

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.machine_first_stop
#print axioms BeaverStructural.BB34.machine_sigma
