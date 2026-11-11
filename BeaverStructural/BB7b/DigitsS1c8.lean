import BeaverStructural.BB7b.Digits
/-! Level-1 summands 136 … 152 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7b

open BeaverStructural.BB7 (sumF)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c8_val : sumF (fun i => f1 (136 + i)) 17 % Mn = 30498041027830851489544276555052487066222273617945019688407842650288827168911641613345310634695646077367202180944734089021603833403822854860709501769954632106332157228978430696682147871098655681379310 := by decide +kernel

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.S1c8_val
