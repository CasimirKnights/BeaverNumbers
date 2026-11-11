import BeaverStructural.BB6.Decimal200PeriodBaseValues
import BeaverStructural.BB6.TowerResidueTable

/-! Shared literal residues of the original period-certificate chain.
Every row is kernel checked from the previous row through the original
power-generator recurrence; literals are never correctness assumptions. -/
namespace BeaverStructural.BB6.Decimal200
set_option compiler.extract_closed false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def periodRow0 : List ℕ := [2, 3, 3, 3]

theorem periodRow0_correct : TowerModulus.residuePrefix chain0=periodRow0 := by
  unfold chain0
  rewrite [TowerModulus.prefix_step, TowerModulus.prefix_one]
  decide +kernel

#check periodRow0_correct

def periodRow1 : List ℕ := [6, 3, 7, 7, 7]

theorem periodRow1_correct : TowerModulus.residuePrefix chain1=periodRow1 := by
  unfold chain1
  rewrite [TowerModulus.prefix_step, periodRow0_correct]
  decide +kernel

#check periodRow1_correct

def periodRow2 : List ℕ := [6, 63, 7, 27, 27, 27]

theorem periodRow2_correct : TowerModulus.residuePrefix chain2=periodRow2 := by
  unfold chain2
  rewrite [TowerModulus.prefix_step, periodRow1_correct]
  decide +kernel

#check periodRow2_correct

def periodRow3 : List ℕ := [6, 63, 307, 127, 227, 227, 227]

theorem periodRow3_correct : TowerModulus.residuePrefix chain3=periodRow3 := by
  unfold chain3
  rewrite [TowerModulus.prefix_step, periodRow2_correct]
  decide +kernel

#check periodRow3_correct

def periodRow4 : List ℕ := [6, 63, 807, 1627, 727, 1227, 1227, 1227]

theorem periodRow4_correct : TowerModulus.residuePrefix chain4=periodRow4 := by
  unfold chain4
  rewrite [TowerModulus.prefix_step, periodRow3_correct]
  decide +kernel

#check periodRow4_correct

def periodRow5 : List ℕ := [6, 63, 807, 4127, 727, 8727, 11227, 11227, 11227]

theorem periodRow5_correct : TowerModulus.residuePrefix chain5=periodRow5 := by
  unfold chain5
  rewrite [TowerModulus.prefix_step, periodRow4_correct]
  decide +kernel

#check periodRow5_correct

def periodRow6 : List ℕ := [6, 63, 25807, 54127, 727, 58727, 36227, 48727, 48727, 48727]

theorem periodRow6_correct : TowerModulus.residuePrefix chain6=periodRow6 := by
  unfold chain6
  rewrite [TowerModulus.prefix_step, periodRow5_correct]
  decide +kernel

#check periodRow6_correct

def periodRow7 : List ℕ := [6, 63, 88307, 179127, 188227, 183727, 223727, 111227, 173727, 173727, 173727]

theorem periodRow7_correct : TowerModulus.residuePrefix chain7=periodRow7 := by
  unfold chain7
  rewrite [TowerModulus.prefix_step, periodRow6_correct]
  decide +kernel

#check periodRow7_correct

def periodRow8 : List ℕ := [6, 63, 88307, 179127, 1438227, 183727, 1161227, 111227, 1111227, 1423727, 1423727, 1423727]

theorem periodRow8_correct : TowerModulus.residuePrefix chain8=periodRow8 := by
  unfold chain8
  rewrite [TowerModulus.prefix_step, periodRow7_correct]
  decide +kernel

#check periodRow8_correct

def periodRow9 : List ℕ := [6, 63, 3213307, 1741627, 4563227, 4871227, 1161227, 3236227, 7361227, 4548727, 6111227, 6111227, 6111227]

theorem periodRow9_correct : TowerModulus.residuePrefix chain9=periodRow9 := by
  unfold chain9
  rewrite [TowerModulus.prefix_step, periodRow8_correct]
  decide +kernel

#check periodRow9_correct

def periodRow10 : List ℕ := [6, 63, 18838307, 25179127, 35813227, 20496227, 32411227, 26673727, 22986227, 12361227, 37361227, 6111227, 6111227, 6111227]

theorem periodRow10_correct : TowerModulus.residuePrefix chain10=periodRow10 := by
  unfold chain10
  rewrite [TowerModulus.prefix_step, periodRow9_correct]
  decide +kernel

#check periodRow10_correct

def periodRow11 : List ℕ := [6, 63, 136025807, 103304127, 74875727, 137683727, 71473727, 104798727, 179236227, 90486227, 76423727, 6111227, 45173727, 45173727, 45173727]

theorem periodRow11_correct : TowerModulus.residuePrefix chain11=periodRow11 := by
  unfold chain11
  rewrite [TowerModulus.prefix_step, periodRow10_correct]
  decide +kernel

#check periodRow11_correct

def periodRow12 : List ℕ := [6, 63, 721963307, 103304127, 465500727, 528308727, 266786227, 300111227, 765173727, 871736227, 76423727, 201423727, 826423727, 45173727, 45173727, 45173727]

theorem periodRow12_correct : TowerModulus.residuePrefix chain12=periodRow12 := by
  unfold chain12
  rewrite [TowerModulus.prefix_step, periodRow11_correct]
  decide +kernel

#check periodRow12_correct

def periodRow13 : List ℕ := [6, 63, 721963307, 103304127, 465500727, 3457996227, 2219911227, 3229798727, 2718298727, 4777986227, 76423727, 4107673727, 826423727, 3951423727, 45173727, 45173727, 45173727]

theorem periodRow13_correct : TowerModulus.residuePrefix chain13=periodRow13 := by
  unfold chain13
  rewrite [TowerModulus.prefix_step, periodRow12_correct]
  decide +kernel

#check periodRow13_correct

def periodRow14 : List ℕ := [6, 63, 15370400807, 4986116627, 465500727, 3457996227, 16868348727, 8112611227, 7601111227, 14543611227, 14724861227, 18756111227, 5709236227, 18599861227, 9810798727, 14693611227, 14693611227, 14693611227]

theorem periodRow14_correct : TowerModulus.residuePrefix chain14=periodRow14 := by
  unfold chain14
  rewrite [TowerModulus.prefix_step, periodRow13_correct]
  decide +kernel

#check periodRow14_correct

def periodRow15 : List ℕ := [6, 63, 88612588307, 53814241627, 98121750727, 101114246227, 65696473727, 105768861227, 32015173727, 38957673727, 112381111227, 18756111227, 78951423727, 91842048727, 58638923727, 14693611227, 39107673727, 39107673727, 39107673727]

theorem periodRow15_correct : TowerModulus.residuePrefix chain15=periodRow15 := by
  unfold chain15
  rewrite [TowerModulus.prefix_step, periodRow14_correct]
  decide +kernel

#check periodRow15_correct

def periodRow16 : List ℕ := [6, 63, 454823525807, 175884554127, 98121750727, 467325183727, 309837098727, 471979798727, 32015173727, 38957673727, 600662361227, 18756111227, 78951423727, 91842048727, 546920173727, 502974861227, 283248298727, 405318611227, 405318611227, 405318611227]

theorem periodRow16_correct : TowerModulus.residuePrefix chain16=periodRow16 := by
  unfold chain16
  rewrite [TowerModulus.prefix_step, periodRow15_correct]
  decide +kernel

#check periodRow16_correct

def periodRow17 : List ℕ := [6, 63, 1675526650807, 175884554127, 98121750727, 2298379871227, 920188661227, 1082331361227, 1863069861227, 38957673727, 600662361227, 1849810798727, 1299654548727, 91842048727, 2377974861227, 502974861227, 893599861227, 2846724861227, 405318611227, 405318611227, 405318611227]

theorem periodRow17_correct : TowerModulus.residuePrefix chain17=periodRow17 := by
  unfold chain17
  rewrite [TowerModulus.prefix_step, periodRow16_correct]
  decide +kernel

#check periodRow17_correct

def periodRow18 : List ℕ := [6, 63, 13882557900807, 6279400179127, 9253395188227, 8401895496227, 10075462098727, 7185846986227, 1863069861227, 12245988923727, 12807693611227, 11005084236227, 13506685798727, 91842048727, 11533248298727, 6606490486227, 6997115486227, 12001998298727, 6508834236227, 9560592048727, 9560592048727, 9560592048727]

theorem periodRow18_correct : TowerModulus.residuePrefix chain18=periodRow18 := by
  unfold chain18
  rewrite [TowerModulus.prefix_step, periodRow17_correct]
  decide +kernel

#check periodRow18_correct

def periodRow19 : List ℕ := [6, 63, 44400136025807, 21538189241627, 9253395188227, 8401895496227, 55851829286227, 68221003236227, 32380647986227, 73281145173727, 73842849861227, 26263873298727, 74541842048727, 61126998298727, 72568404548727, 37124068611227, 22255904548727, 73037154548727, 37026412361227, 9560592048727, 24819381111227, 24819381111227, 24819381111227]

theorem periodRow19_correct : TowerModulus.residuePrefix chain19=periodRow19 := by
  unfold chain19
  rewrite [TowerModulus.prefix_step, periodRow18_correct]
  decide +kernel

#check periodRow19_correct

end BeaverStructural.BB6.Decimal200
