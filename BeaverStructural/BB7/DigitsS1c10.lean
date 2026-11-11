import BeaverStructural.BB7.Digits
/-! Level-1 summands 170 … 186 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c10_val : sumF (fun i => term1 (170 + i)) 17 % M = 96933823254193755062373713557818620253227401209440892562917352154995536294248693248795396390795721819433667131676298018025465041204219069968746358737514306394642353660499686884641215863929663375013590 := by decide +kernel

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.S1c10_val
