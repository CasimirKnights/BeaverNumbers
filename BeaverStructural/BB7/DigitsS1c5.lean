import BeaverStructural.BB7.Digits
/-! Level-1 summands 85 … 101 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c5_val : sumF (fun i => term1 (85 + i)) 17 % M = 44093002857661331988440155378569629857871365108756350369674687726369810989458417912992869168830528175372712886474378018025465041204219069968746358737514306394642353660499686884641215863929663375013590 := by decide +kernel

end BeaverStructural.BB7

#print axioms BeaverStructural.BB7.S1c5_val
