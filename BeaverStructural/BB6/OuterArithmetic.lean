import BeaverStructural.BB6.Bulk

namespace BeaverStructural.BB6

def modeAfter (j : ℕ) : ℕ := 2-j%3
def widthAfter (j b : ℕ) : ℕ := towerSum (j+1) b + 5*(j/3)+2*(j%3)

theorem modeAfter_lt (j : ℕ) : modeAfter j < 3 := by unfold modeAfter; omega

theorem modeAfter_succ (j : ℕ) : modeAfter (j+1) = (modeAfter j+2)%3 := by
  unfold modeAfter
  omega

theorem widthAfter_zero (b : ℕ) : widthAfter 0 b = b := by
  simp [widthAfter, towerSum, tower]

theorem widthAfter_succ (j b : ℕ) :
    widthAfter (j+1) b = widthAfter j b + tower (j+1) b +
      (if modeAfter j = 0 then 1 else 2) := by
  have ht : towerSum (j+1+1) b = towerSum (j+1) b + tower (j+1) b := by
    exact Finset.sum_range_succ _ _
  unfold widthAfter
  rw [ht]
  unfold modeAfter
  split <;> omega

/-- Mode and width corrections account for every primitive instruction in
the original positive-outer macro cost. -/
theorem width_mode_cost (j b : ℕ) :
    12*widthAfter j b+4*modeAfter j+63 = 12*towerSum (j+1) b+20*j+71 := by
  unfold widthAfter modeAfter
  omega

theorem phaseCost_from_macro (n b j : ℕ) :
    (phaseCost n b j : ℤ) =
      6*(tower (j+2) b : ℤ)^2+54*tower (j+2) b+
      12*widthAfter j b+4*modeAfter j-9*tower (j+1) b+63+
      12*padicValNat 2 (n-j) := by
  rw [phaseCost_counted_polynomial]
  have hh := congrArg (fun n : ℕ => (n : ℤ)) (width_mode_cost j b)
  push_cast at hh
  linarith

end BeaverStructural.BB6
