import BeaverStructural.BB34.Digits
/-! Level-1 summands 102 … 118 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB34

open BeaverStructural.BB7 (sumF M)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c6_val : sumF (fun i => term1 (102 + i)) 17 % M = 25634481254698827385578790608365402539095781333395624908456902578747853769448573957006692593855790258540252442266969515749319939839749109455936672347207401306534721997962404643352638386221727370357345 := by decide +kernel

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.S1c6_val
