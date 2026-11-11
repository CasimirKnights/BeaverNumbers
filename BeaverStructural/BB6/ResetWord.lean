import BeaverStructural.BB6.CounterTape

namespace BeaverStructural.BB6

/-- Exact outer word produced by resetting a zero counter. No counter digits
are discarded: the single zero digit separates two maximal-one blocks. -/
theorem counterWord_reset (L a : ℕ) :
    counterWord (L+a+2) (2^(L+a+2)-2^a-1) =
      oneBlocks (L+1) ++ [true,true,true] ++ oneBlocks a := by
  have hp : 0 < 2^a := by positivity
  have hl : 2 ≤ 2^(L+2) := by
    have hh : 2^1 ≤ (2:ℕ)^(L+2) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using hh
  have hv : 2^(L+a+2)-2^a-1 = (2^(L+2)-2)*2^a+(2^a-1) := by
    have he : 2^(L+a+2) = 2^(L+2)*2^a := by rw [← pow_add]; congr 1; omega
    rw [he]
    have hs : 2^(L+2) = (2^(L+2)-2)+2 := by omega
    calc 2^(L+2)*2^a-2^a-1 = ((2^(L+2)-2)+2)*2^a-2^a-1 := by nth_rw 1 [hs]
      _ = _ := by rw [Nat.add_mul]; omega
  have hs : 2^(L+2)-2 = (2^(L+1)-1)*2 := by
    have hpos : 0 < (2:ℕ)^(L+1) := by positivity
    rw [show L+2=(L+1)+1 by omega, pow_succ]
    omega
  rw [hv, show L+a+2=(L+2)+a by omega, counterWord_one_suffix, hs]
  have hw : counterWord (L+2) ((2^(L+1)-1)*2) =
      counterWord (L+1) (2^(L+1)-1) ++ [true,true,true] := by
    simpa using counterWord_zero_suffix (L+1) 1 (2^(L+1)-1)
  rw [hw, counterWord_max]

end BeaverStructural.BB6
