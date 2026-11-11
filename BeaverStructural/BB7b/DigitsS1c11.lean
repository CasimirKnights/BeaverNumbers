import BeaverStructural.BB7b.Digits
/-! Level-1 summands 187 … 203 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7b

open BeaverStructural.BB7 (sumF)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c11_val : sumF (fun i => f1 (187 + i)) 17 % Mn = 6524849255907822456258417149677314576805052797560695700871709883988547877171382737761308242154385642173950885650720031015280236482916013700672397874843313736420074731902861854564611141200560934305600 := by decide +kernel

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.S1c11_val
