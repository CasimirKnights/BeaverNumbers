import BeaverStructural.BB34.Digits
/-! Level-1 summands 68 … 84 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB34

open BeaverStructural.BB7 (sumF M)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c4_val : sumF (fun i => term1 (68 + i)) 17 % M = 85834598628210359454816604610957441064153752101384298450825014016821586172672067129727111302634217992649373059901595048931078162994949109455936672347207401306534721997962404643352638386221727370357345 := by decide +kernel

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.S1c4_val
