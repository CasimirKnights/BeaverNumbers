import BeaverStructural.BB6.DecimalResidues

namespace BeaverStructural.BB6

set_option compiler.extract_closed false
attribute [local irreducible] tower

/-- A finite certificate tree of exact periods of the power generator. -/
inductive TowerModulus : ℕ → Type
  | one : TowerModulus 1
  | step {m p : ℕ} (child : TowerModulus p) (hm : 0<m) (hp : 0<p)
      (period : modularPower 2 (200+p) m=modularPower 2 200 m) : TowerModulus m

namespace TowerModulus

def depth {m : ℕ} : TowerModulus m → ℕ
  | .one => 0
  | .step child _ _ _ => child.depth+1

def residue {m : ℕ} : TowerModulus m → ℕ → ℕ
  | .one, _ => 0
  | .step (p:=p) child _ _ _, h =>
    if h=0 then 6%m else if h=1 then 63%m else if h=2 then 9223372036854775807%m
    else (modularPower 2 (child.residue (h-1)+200*p) m+m-1)%m

def steady {m : ℕ} : TowerModulus m → ℕ
  | .one => 0
  | .step (p:=p) child _ _ _ =>
    (modularPower 2 (child.steady+200*p) m+m-1)%m

theorem pow_pred_mod (m n : ℕ) (hm : 0<m) :
    (2^n-1)%m=(modularPower 2 n m+m-1)%m := by
  rw [modularPower_eq]
  have hp : 0<(2:ℕ)^n := by positivity
  have he : 2^n%m=(2^n%m+m)%m := by simp
  exact Nat.ModEq.sub hp (by omega) he (Nat.ModEq.refl 1)

theorem tower_two_large : 200≤tower 2 6 := by
  rw [tower_succ,tower_succ,tower_zero]
  norm_num

theorem tower_exponent_large (h : ℕ) (hh : 3≤h) : 200≤tower (h-1) 6 :=
  tower_two_large.trans (tower_monotone 6 (by omega))

theorem residue_correct {m : ℕ} (C : TowerModulus m) (h : ℕ) :
    tower h 6%m=C.residue h := by
  induction C generalizing h with
  | one => simp only [residue, Nat.mod_one]
  | @step m p child hm hp period ih =>
    simp only [residue]
    split_ifs with h0 h1 h2
    · subst h; rw [tower_zero]
    · subst h; rw [tower_succ,tower_zero]; norm_num
    · subst h; rw [tower_succ,tower_succ,tower_zero]; norm_num
    · have hh : 3≤h := by omega
      have hn := tower_exponent_large h hh
      have hr : 200≤child.residue (h-1)+200*p := by omega
      have he : tower (h-1) 6%p=(child.residue (h-1)+200*p)%p := by
        rw [ih]
        have hb : child.residue (h-1)%p=child.residue (h-1) := by rw [← ih, Nat.mod_mod]
        simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,
          Nat.add_zero,Nat.mod_mod,hb]
      have hperiod : 2^(200+p)%m=2^200%m := by simpa only [modularPower_eq] using period
      have hx := pow2_mod_of_congruent m 200 p (tower (h-1) 6)
        (child.residue (h-1)+200*p) hn hr hperiod he
      have ht : tower h 6=2^tower (h-1) 6-1 := by
        conv_lhs => rw [show h=(h-1)+1 by omega]
        rw [tower_succ]
      rw [ht,pow_pred_mod m _ hm]
      rw [modularPower_eq,modularPower_eq,hx]


theorem steady_correct {m : ℕ} (C : TowerModulus m) (h : ℕ) (hh : C.depth+2≤h) :
    tower h 6%m=C.steady := by
  induction C generalizing h with
  | one => simp only [steady,Nat.mod_one]
  | @step m p child hm hp period ih =>
    have hdepth : child.depth+1+2≤h := hh
    have hn := tower_exponent_large h (by omega)
    have hr : 200≤child.steady+200*p := by omega
    have hc : tower (h-1) 6%p=child.steady := ih (h-1) (by omega)
    have hres : child.steady%p=child.steady := by rw [← hc,Nat.mod_mod]
    have he : tower (h-1) 6%p=(child.steady+200*p)%p := by
      rw [hc]
      simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_self,Nat.mul_zero,Nat.zero_mod,
        Nat.add_zero,Nat.mod_mod,hres]
    have hperiod : 2^(200+p)%m=2^200%m := by simpa only [modularPower_eq] using period
    have hx := pow2_mod_of_congruent m 200 p (tower (h-1) 6)
      (child.steady+200*p) hn hr hperiod he
    have ht : tower h 6=2^tower (h-1) 6-1 := by
      conv_lhs => rw [show h=(h-1)+1 by omega]
      rw [tower_succ]
    rw [ht,pow_pred_mod m _ hm]
    simp only [steady,modularPower_eq,hx]

end TowerModulus
end BeaverStructural.BB6
