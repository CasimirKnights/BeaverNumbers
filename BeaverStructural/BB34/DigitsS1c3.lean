import BeaverStructural.BB34.Digits
/-! Level-1 summands 51 … 67 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB34

open BeaverStructural.BB7 (sumF M)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c3_val : sumF (fun i => term1 (51 + i)) 17 % M = 88859031190712040080171335327810175907895168841412939943047789169186733981275907113886998427858064586667581534910806248160958254777728347802623922779207401306534721997962404643352638386221727370357345 := by decide +kernel

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.S1c3_val
