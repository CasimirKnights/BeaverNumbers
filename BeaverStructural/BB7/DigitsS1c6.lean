import BeaverStructural.BB7.Digits
/-! Level-1 summands 102 … 118 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c6_val : sumF (fun i => term1 (102 + i)) 17 % M = 39822348422360002656918159439089541754727012422243382089704523499157066939311257510387380751972809819433667131676298018025465041204219069968746358737514306394642353660499686884641215863929663375013590 := by decide +kernel

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.S1c6_val
