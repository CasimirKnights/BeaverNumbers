import BeaverStructural.BB7.Digits
/-! Level-1 summands 0 … 16 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c0_val : sumF (fun i => term1 (0 + i)) 17 % M = 82273665848033208124343407822992927407641365262133866953102174391509847814768708202578545976276705443786878697436009130981459549119681539465296776295699518876962866202288419835881133014128118984344078 := by decide +kernel

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.S1c0_val
