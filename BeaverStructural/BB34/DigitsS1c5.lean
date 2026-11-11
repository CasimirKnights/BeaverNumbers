import BeaverStructural.BB34.Digits
/-! Level-1 summands 85 … 101 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB34

open BeaverStructural.BB7 (sumF M)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c5_val : sumF (fun i => term1 (85 + i)) 17 % M = 36864286450047636095587871929385816103739581361664448781761334539993875015184688722306226680084804621206130963385689515749319939839749109455936672347207401306534721997962404643352638386221727370357345 := by decide +kernel

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.S1c5_val
