import BeaverStructural.BB7b.Digits
/-! Level-1 summands 34 … 50 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7b

open BeaverStructural.BB7 (sumF)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c2_val : sumF (fun i => f1 (34 + i)) 17 % Mn = 53838184303210048473078510968383280249086867684374888523438500388276455760755919100767749566473854166122137535897848059902354994979055662352848319676334331813363407228978430696682147871098655681379310 := by decide +kernel

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.S1c2_val
