import BeaverStructural.BB7b.Digits
/-! Level-1 summands 68 … 84 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7b

open BeaverStructural.BB7 (sumF)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c4_val : sumF (fun i => f1 (68 + i)) 17 % Mn = 18870425145658189348085447464889846374027269268024700461920790458750144154599304730430779062986796721694192185573630802278439770903822854860709501769954632106332157228978430696682147871098655681379310 := by decide +kernel

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.S1c4_val
