import BeaverStructural.BB34.Digits
/-! Level-1 summands 0 … 16 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB34

open BeaverStructural.BB7 (sumF M)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c0_val : sumF (fun i => term1 (0 + i)) 17 % M = 46752043727468550406701301117387844725885264298527519286743567163448724232866455517532271637649633490789062341281888784747851276394877679240045171623636057172290114815218781901700141669535964103661137 := by decide +kernel

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.S1c0_val
