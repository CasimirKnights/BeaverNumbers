import BeaverStructural.BB34.Digits
/-! Level-1 summands 17 … 33 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB34

open BeaverStructural.BB7 (sumF M)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c1_val : sumF (fun i => term1 (17 + i)) 17 % M = 94865177879191178202445927052677458324389410477370286357553727419343475582696645590334710684349729310525977882743541293274790715517282153703290275491337355201687570760327761591362417586221727370357345 := by decide +kernel

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.S1c1_val
