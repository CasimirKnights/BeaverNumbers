import BeaverStructural.BB7.Digits
/-! Level-1 summands 119 … 135 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c7_val : sumF (fun i => term1 (119 + i)) 17 % M = 55442507234035724444440561190742124261609456115204913595483424965210568107740610048795396390795721819433667131676298018025465041204219069968746358737514306394642353660499686884641215863929663375013590 := by decide +kernel

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.S1c7_val
