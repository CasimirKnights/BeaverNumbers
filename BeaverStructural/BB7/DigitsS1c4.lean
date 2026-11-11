import BeaverStructural.BB7.Digits
/-! Level-1 summands 68 … 84 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c4_val : sumF (fun i => term1 (68 + i)) 17 % M = 78556123836989387810897164838211632381342347781108459640701558689480674217907382703030677072882505008020683248353097536971745435137019069968746358737514306394642353660499686884641215863929663375013590 := by decide +kernel

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.S1c4_val
