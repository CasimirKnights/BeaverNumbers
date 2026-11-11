import BeaverStructural.BB34.Digits
/-! Level-1 summands 170 … 186 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB34

open BeaverStructural.BB7 (sumF M)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c10_val : sumF (fun i => term1 (170 + i)) 17 % M = 88063992934444429928809066972080388686147883843578997518134240859606724320326414883200619925892398258540252442266969515749319939839749109455936672347207401306534721997962404643352638386221727370357345 := by decide +kernel

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.S1c10_val
