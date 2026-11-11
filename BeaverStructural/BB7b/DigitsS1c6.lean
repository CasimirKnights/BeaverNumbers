import BeaverStructural.BB7b.Digits
/-! Level-1 summands 102 … 118 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7b

open BeaverStructural.BB7 (sumF)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c6_val : sumF (fun i => f1 (102 + i)) 17 % Mn = 48764270843030757413350050663161616771518800642327033810291630899367688723064905182223484462820646077367202180944734089021603833403822854860709501769954632106332157228978430696682147871098655681379310 := by decide +kernel

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.S1c6_val
