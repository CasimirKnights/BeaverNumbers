import BeaverStructural.BB34.Digits
/-! Level-1 summands 34 … 50 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB34

open BeaverStructural.BB7 (sumF M)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c2_val : sumF (fun i => term1 (34 + i)) 17 % M = 73251502098471727298336345553286782136202312453337602060288001928970697256222092726292829492808055638519397872615181550531617469183348346282673173092898844288818887117962404643352638386221727370357345 := by decide +kernel

end BeaverStructural.BB34

#print axioms BeaverStructural.BB34.S1c2_val
