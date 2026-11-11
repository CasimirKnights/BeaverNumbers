import BeaverStructural.BB7.Digits
/-! Level-1 summands 136 … 152 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c8_val : sumF (fun i => term1 (136 + i)) 17 % M = 88139211145911155050927755832312051789364419925247632681924092634995536294248693248795396390795721819433667131676298018025465041204219069968746358737514306394642353660499686884641215863929663375013590 := by decide +kernel

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.S1c8_val
