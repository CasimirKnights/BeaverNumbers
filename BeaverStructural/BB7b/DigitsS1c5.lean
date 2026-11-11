import BeaverStructural.BB7b.Digits
/-! Level-1 summands 85 … 101 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7b

open BeaverStructural.BB7 (sumF)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c5_val : sumF (fun i => f1 (85 + i)) 17 % Mn = 19548048291944454297244689227171241087490081788770290368613091405094834636009016237058534322825338439109986041900720031015280236482916013700672397874843313736420074731902861854564611141200560934305600 := by decide +kernel

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.S1c5_val
