import BeaverStructural.BB6.Residues

/-! Computable modular assembly of the actual counted clock polynomial.
Padded modular subtraction is justified by the original natural subtraction
bounds, and residue bounds are derived from the supplied equalities. -/
namespace BeaverStructural.BB6

namespace ModularClock

def modSub (m a b : ℕ) : ℕ := (a+m-b)%m

def bulkCode (m nr sq lin er fr tw cr : ℕ) : ℕ :=
  (6*sq+45*lin+9*modSub m er fr+6*tw+10*nr^2+61*nr+12*cr)%m

def resetCode (m Lr ar br sr : ℕ) : ℕ :=
  (6*sr^2+45*sr+9*modSub m sr br+12*Lr+12*ar+97)%m

def haltCode (m Lr ar : ℕ) : ℕ := (12*Lr+12*ar+60)%m

def clockCode (m bulk0 reset0 bulk1 reset1 bulk2 halt2 : ℕ) : ℕ :=
  (27965+bulk0+reset0+bulk1+reset1+bulk2+halt2)%m

theorem modSub_correct (m a b ar br : ℕ) (hm : 0<m) (hab : b≤a)
    (ha : a%m=ar) (hb : b%m=br) : (a-b)%m=modSub m ar br := by
  have hbr : br<m := by rw [← hb]; exact Nat.mod_lt _ hm
  have har : a ≡ ar [MOD m] := by change a%m=ar%m; rw [← ha,Nat.mod_mod]
  have hbr' : b ≡ br [MOD m] := by change b%m=br%m; rw [← hb,Nat.mod_mod]
  have harr : ar ≡ ar+m [MOD m] := by simp [Nat.ModEq]
  exact Nat.ModEq.sub hab (by omega : br≤ar+m) (har.trans harr) hbr'

theorem bulkCode_correct (m n b nr sq lin er fr tw cr : ℕ) (hm : 0<m)
    (hn : n%m=nr) (hsq : towerSquareSum n (tower 2 b)%m=sq)
    (hlin : towerSum n (tower 2 b)%m=lin)
    (her : tower (n+1) b%m=er) (hfr : tower 1 b%m=fr)
    (htw : (2*towerWeightedSum n b)%m=tw) (hcr : binaryCarry n%m=cr) :
    bulkCost n b%m=bulkCode m nr sq lin er fr tw cr := by
  have hd := modSub_correct m (tower (n+1) b) (tower 1 b) er fr hm
    (tower_monotone b (by omega)) her hfr
  have hw : (12*towerWeightedSum n b)%m=(6*tw)%m := by
    have h : 2*towerWeightedSum n b ≡ tw [MOD m] := by
      change (2*towerWeightedSum n b)%m=tw%m
      rw [← htw,Nat.mod_mod]
    simpa only [Nat.ModEq, ← Nat.mul_assoc] using h.mul_left 6
  unfold bulkCost bulkCode
  simp only [Nat.add_mod,Nat.mod_mod]
  rw [hw]
  simp only [Nat.mul_mod,Nat.pow_mod,hsq,hlin,hd,hn,hcr,Nat.add_mod,Nat.mod_mod]

theorem resetCode_correct (m L a b Lr ar br sr : ℕ) (hm : 0<m)
    (hL : L%m=Lr) (ha : a%m=ar) (hb : b%m=br) (hs : (2^b-1)%m=sr) :
    resetCost L a b%m=resetCode m Lr ar br sr := by
  have hbs : b≤2^b-1 := by have := self_lt_two_pow b; omega
  have hd := modSub_correct m (2^b-1) b sr br hm hbs hs hb
  unfold resetCost resetCode
  simp only [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,hL,ha,hs,hd,Nat.mod_mod]

theorem haltCode_correct (m L a Lr ar : ℕ)
    (hL : L%m=Lr) (ha : a%m=ar) : haltCost L a%m=haltCode m Lr ar := by
  unfold haltCost haltCode
  simp only [Nat.add_mod,Nat.mul_mod,hL,ha,Nat.mod_mod]

theorem clockCode_correct (m : ℕ) (C0 C1 C2 : Counter)
    (b0 r0 b1 r1 b2 h2 : ℕ)
    (hb0 : bulkCost C0.count C0.base%m=b0)
    (hr0 : resetCost C0.length (exhaustedWidth C0) (exhaustedRight C0)%m=r0)
    (hb1 : bulkCost C1.count C1.base%m=b1)
    (hr1 : resetCost C1.length (exhaustedWidth C1) (exhaustedRight C1)%m=r1)
    (hb2 : bulkCost C2.count C2.base%m=b2)
    (hh2 : haltCost C2.length (exhaustedWidth C2)%m=h2) :
    clockFor C0 C1 C2%m=clockCode m b0 r0 b1 r1 b2 h2 := by
  unfold clockFor clockCode
  simp only [Nat.add_mod,hb0,hr0,hb1,hr1,hb2,hh2,Nat.mod_mod]

end ModularClock
end BeaverStructural.BB6
