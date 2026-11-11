import BeaverStructural.BB34.Digits
/-! Level-1 summands 119 … 135 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB34

open BeaverStructural.BB7 (sumF M)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c7_val : sumF (fun i => term1 (119 + i)) 17 % M = 16752160110567644527198094759909074024602831971480803678455732282652158292764226083200619925892398258540252442266969515749319939839749109455936672347207401306534721997962404643352638386221727370357345 := by decide +kernel

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.S1c7_val
