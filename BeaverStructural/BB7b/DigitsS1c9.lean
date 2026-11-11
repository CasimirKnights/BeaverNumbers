import BeaverStructural.BB7b.Digits
/-! Level-1 summands 153 … 169 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7b

open BeaverStructural.BB7 (sumF)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c9_val : sumF (fun i => f1 (153 + i)) 17 % Mn = 40149239326603930979665436824455299195945677797560695700871709883988547877171382737761308242154385642173950885650720031015280236482916013700672397874843313736420074731902861854564611141200560934305600 := by decide +kernel

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.S1c9_val
