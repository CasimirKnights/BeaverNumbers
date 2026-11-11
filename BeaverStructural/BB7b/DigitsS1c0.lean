import BeaverStructural.BB7b.Digits
/-! Level-1 summands 0 … 16 mod 10^200, by kernel evaluation. -/

namespace BeaverStructural.BB7b

open BeaverStructural.BB7 (sumF)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem S1c0_val : sumF (fun i => f1 (0 + i)) 17 % Mn = 26984004010235392993632495878177090082788120228026616097376642440265912562311513555315536563212520086021975221648774954218072241776735455796888594686279635683554115004102114013907016324417861929239110 := by decide +kernel

end BeaverStructural.BB7b

#print axioms BeaverStructural.BB7b.S1c0_val
