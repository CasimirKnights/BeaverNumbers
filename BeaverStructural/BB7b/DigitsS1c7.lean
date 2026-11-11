import BeaverStructural.BB7b.Digits
/-! Level-1 summands 119 … 135 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7b

open BeaverStructural.BB7 (sumF)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c7_val : sumF (fun i => f1 (119 + i)) 17 % Mn = 19170657383764013258609952381358312571007550533743217904179308713257957056858882737761308242154385642173950885650720031015280236482916013700672397874843313736420074731902861854564611141200560934305600 := by decide +kernel

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.S1c7_val
