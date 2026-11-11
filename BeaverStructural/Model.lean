import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace BeaverStructural

structure Row (Q : Type) where
  write : Bool
  move : ℤ
  next : Option Q

structure Config (Q : Type) where
  state : Option Q
  tape : ℤ → Bool
  head : ℤ
  clock : ℕ

variable {Q : Type}

def step (δ : Q → Bool → Row Q) (c : Config Q) : Config Q :=
  match c.state with
  | none => c
  | some q =>
    { state := (δ q (c.tape c.head)).next
      tape := Function.update c.tape c.head (δ q (c.tape c.head)).write
      head := c.head + (δ q (c.tape c.head)).move
      clock := c.clock + 1 }

theorem step_stopped (δ : Q → Bool → Row Q) (c : Config Q) (h : c.state = none) :
    step δ c = c := by
  simp [step, h]

theorem step_active_clock (δ : Q → Bool → Row Q) (c : Config Q) (q : Q) (h : c.state = some q) :
    (step δ c).clock = c.clock + 1 := by
  simp [step, h]

def Stopped (δ : Q → Bool → Row Q) (n : ℕ) (c : Config Q) : Prop :=
  ((step δ)^[n] c).state = none

theorem stopped_succ (δ : Q → Bool → Row Q) (c : Config Q) (n : ℕ) (h : Stopped δ n c) :
    Stopped δ (n + 1) c := by
  unfold Stopped at *
  rw [Function.iterate_succ_apply', step_stopped δ _ h]
  exact h

theorem stopped_mono (δ : Q → Bool → Row Q) (c : Config Q) {n m : ℕ} (h : Stopped δ n c)
    (hnm : n ≤ m) : Stopped δ m c := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact stopped_succ δ c k ih

def FirstHit (δ : Q → Bool → Row Q) (n : ℕ) (c : Config Q) : Prop :=
  Stopped δ n c ∧ ∀ k < n, ¬ Stopped δ k c

theorem iterate_clock (δ : Q → Bool → Row Q) (c : Config Q) (n : ℕ)
    (hact : ∀ k < n, ¬ Stopped δ k c) : ((step δ)^[n] c).clock = c.clock + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : ¬ Stopped δ n c := hact n (Nat.lt_succ_self n)
    rw [Function.iterate_succ_apply']
    cases hs : ((step δ)^[n] c).state with
    | none => exact absurd hs hn
    | some q =>
      rw [step_active_clock δ _ q hs, ih (fun k hk => hact k (Nat.lt_succ_of_lt hk))]
      ring

end BeaverStructural

namespace BeaverStructural.BorrowCompletion

theorem quotient_pos (c k : ℕ) (hc : 0 < c) (hk : k ≤ padicValNat 2 c) :
    0 < c / 2 ^ k := by
  haveI := Fact.mk Nat.prime_two
  have hd : 2 ^ k ∣ c := (padicValNat_dvd_iff_le hc.ne').2 hk
  exact Nat.div_pos (Nat.le_of_dvd hc hd) (by positivity)

theorem quotient_odd_at (c : ℕ) (hc : 0 < c) :
    (c / 2 ^ padicValNat 2 c) % 2 = 1 := by
  haveI := Fact.mk Nat.prime_two
  have hq := quotient_pos c (padicValNat 2 c) hc le_rfl
  have hv : padicValNat 2 (c / 2 ^ padicValNat 2 c) = 0 := by
    rw [padicValNat.div_pow pow_padicValNat_dvd, Nat.sub_self]
  have hn : ¬ 2 ∣ c / 2 ^ padicValNat 2 c := by
    intro hd
    have h : 1 ≤ padicValNat 2 (c / 2 ^ padicValNat 2 c) :=
      (padicValNat_dvd_iff_le hq.ne').1 (by simpa using hd)
    omega
  have hmod := Nat.mod_lt (c / 2 ^ padicValNat 2 c) (by decide : 0 < 2)
  have hne : (c / 2 ^ padicValNat 2 c) % 2 ≠ 0 := by
    intro h; exact hn (Nat.dvd_of_mod_eq_zero h)
  omega

end BeaverStructural.BorrowCompletion
