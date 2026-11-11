import BeaverStructural.BB7.Digits
/-! Level-1 summands 51 … 67 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c3_val : sumF (fun i => term1 (51 + i)) 17 % M = 48299127308791897753895234197603398806964206655947541364889988063468977495620537379597520749438305335267063191603488473099331106103549663664524306385514306394642353660499686884641215863929663375013590 := by decide +kernel

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.S1c3_val
