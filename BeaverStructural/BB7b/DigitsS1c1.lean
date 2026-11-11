import BeaverStructural.BB7b.Digits
/-! Level-1 summands 17 … 33 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7b

open BeaverStructural.BB7 (sumF)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c1_val : sumF (fun i => f1 (17 + i)) 17 % Mn = 51005128139783964891058564799942303709452290353686637819462278821601305741612979921239837438914496635206837712985749313217097439857277118256164471564057750589357516068832183143627111141200560934305600 := by decide +kernel

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.S1c1_val
