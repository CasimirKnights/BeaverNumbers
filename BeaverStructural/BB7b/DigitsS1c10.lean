import BeaverStructural.BB7b.Digits
/-! Level-1 summands 170 … 186 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7b

open BeaverStructural.BB7 (sumF)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c10_val : sumF (fun i => f1 (170 + i)) 17 % Mn = 57946033577365231736514265536272954460672953039369885411064092650288827168911641613345310634695646077367202180944734089021603833403822854860709501769954632106332157228978430696682147871098655681379310 := by decide +kernel

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.S1c10_val
