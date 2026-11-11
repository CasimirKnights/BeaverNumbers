import BeaverStructural.BB34.Digits
/-! Level-1 summands 136 … 152 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB34

open BeaverStructural.BB7 (sumF M)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c8_val : sumF (fun i => term1 (136 + i)) 17 % M = 47780574998049400334941954857976048461567411956143467211360921179606724320326414883200619925892398258540252442266969515749319939839749109455936672347207401306534721997962404643352638386221727370357345 := by decide +kernel

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.S1c8_val
