import BeaverStructural.BB6.Tape
import BeaverStructural.Model

namespace BeaverStructural.BB6

def oneBlocks (k : ℕ) : List Bool := (List.replicate k [true,false,false]).flatten

theorem oneBlocks_succ (k : ℕ) : oneBlocks (k+1) = oneBlocks k ++ [true,false,false] := by
  simp [oneBlocks, List.replicate_succ', List.flatten_append]

theorem counterWord_zero (L : ℕ) : counterWord L 0 = List.replicate (3*L) true := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [counterWord, Nat.zero_div, Nat.zero_mod, if_true, ih]
    rw [Nat.mul_add, List.replicate_add]
    rfl

theorem counterWord_zero_suffix (a k v : ℕ) :
    counterWord (a+k) (v*2^k) = counterWord a v ++ List.replicate (3*k) true := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hd : v*2^(k+1)/2 = v*2^k := by rw [pow_succ, ← Nat.mul_assoc, Nat.mul_div_left _ (by decide)]
    have hm : (v*2^(k+1))%2 = 0 := by rw [pow_succ, ← Nat.mul_assoc]; omega
    rw [Nat.add_succ, counterWord, hd, hm, if_pos rfl, ih]
    rw [Nat.mul_add, List.replicate_add, List.append_assoc]
    rfl

theorem counterWord_one_suffix (a k v : ℕ) :
    counterWord (a+k) (v*2^k+(2^k-1)) = counterWord a v ++ oneBlocks k := by
  induction k with
  | zero => simp [oneBlocks]
  | succ k ih =>
    have hp : 0 < 2^k := by positivity
    have hv : v*2^(k+1) = (v*2^k)*2 := by ring
    have hn : v*2^(k+1)+(2^(k+1)-1) = 2*(v*2^k+(2^k-1))+1 := by
      rw [hv, pow_succ]
      omega
    rw [Nat.add_succ, counterWord, hn]
    have hd : (2*(v*2^k+(2^k-1))+1)/2 = v*2^k+(2^k-1) := by omega
    have hm : (2*(v*2^k+(2^k-1))+1)%2 = 1 := by omega
    simp only [hd, hm, Nat.reduceEqDiff, if_false, ih, oneBlocks_succ, List.append_assoc]

theorem counterWord_max (L : ℕ) : counterWord L (2^L-1) = oneBlocks L := by
  simpa [counterWord] using counterWord_one_suffix 0 L 0

/-- The same unchanged prefix surrounds the unique decrementing bit. Zero
counter digits below it become one digits; every physical bit is retained. -/
theorem counterWord_decrement (L v : ℕ) (hv : 0 < v) (hL : v < 2^L) :
    let k := padicValNat 2 v
    let pre := counterWord (L-k-1) (v / 2^k / 2)
    counterWord L v = pre ++ [true,false,false] ++ List.replicate (3*k) true ∧
    counterWord L (v-1) = pre ++ [true,true,true] ++ oneBlocks k := by
  dsimp only
  let k := padicValNat 2 v
  let q := v / 2^k
  have hd : 2^k ∣ v := pow_padicValNat_dvd
  have hpow : 2^k ≤ v := Nat.le_of_dvd hv hd
  have hk : k < L := by
    by_contra hn
    have hh : 2^L ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hq : q%2=1 := BorrowCompletion.quotient_odd_at v hv
  have hqp : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz] at hq
    contradiction
  have hmul : q*2^k = v := Nat.div_mul_cancel hd
  have hl : L = (L-k-1+1)+k := by omega
  have hp : counterWord (L-k-1+1) q =
      counterWord (L-k-1) (q/2) ++ [true,false,false] := by
    rw [counterWord, hq]
    rfl
  have hp' : counterWord (L-k-1+1) (q-1) =
      counterWord (L-k-1) (q/2) ++ [true,true,true] := by
    have hmod : (q-1)%2=0 := by omega
    have hdiv : (q-1)/2=q/2 := by omega
    rw [counterWord, hmod, hdiv]
    rfl
  have hsub : v-1 = (q-1)*2^k+(2^k-1) := by
    have hh : q = (q-1)+1 := by omega
    have he : v = (q-1)*2^k+2^k := by
      calc v = q*2^k := hmul.symm
        _ = ((q-1)+1)*2^k := congrArg (fun a => a*2^k) hh
        _ = _ := by ring
    have hz : 0 < 2^k := by positivity
    omega
  constructor
  · change counterWord L v = _
    calc counterWord L v = counterWord ((L-k-1+1)+k) (q*2^k) := by rw [← hl, hmul]
      _ = _ := by rw [counterWord_zero_suffix, hp]
  · change counterWord L (v-1) = _
    calc counterWord L (v-1) = counterWord ((L-k-1+1)+k) ((q-1)*2^k+(2^k-1)) := by rw [← hl, ← hsub]
      _ = _ := by rw [counterWord_one_suffix, hp']

end BeaverStructural.BB6
