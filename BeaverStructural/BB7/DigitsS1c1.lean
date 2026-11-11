import BeaverStructural.BB7.Digits
/-! Level-1 summands 17 … 33 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c1_val : sumF (fun i => term1 (17 + i)) 17 % M = 97525193306487524258066413280271468807771121744200851845306354729634905562757758164286156727468587160739830324610086525949306682448526861103218129652615086204829443923785468284819084663929663375013590 := by decide +kernel

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.S1c1_val
