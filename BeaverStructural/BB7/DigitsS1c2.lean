import BeaverStructural.BB7.Digits
/-! Level-1 summands 34 … 50 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c2_val : sumF (fun i => term1 (34 + i)) 17 % M = 13581122102183292453850645676707478344011498753116527281157607517472068925277727647601268026684662078097358531463911108752230134268233847328066177455125243457616121340499686884641215863929663375013590 := by decide +kernel

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.S1c2_val
