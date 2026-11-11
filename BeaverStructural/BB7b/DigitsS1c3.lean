import BeaverStructural.BB7b.Digits
/-! Level-1 summands 51 … 67 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7b

open BeaverStructural.BB7 (sumF)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c3_val : sumF (fun i => f1 (51 + i)) 17 % Mn = 54408301059707985570702583879054844804967308430195167984930174090126751024328550465088083311295567889316446737394579733780174118459520475370594272874843313736420074731902861854564611141200560934305600 := by decide +kernel

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.S1c3_val
