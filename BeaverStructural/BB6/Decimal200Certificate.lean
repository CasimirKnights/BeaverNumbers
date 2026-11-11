import BeaverStructural.BB6.Decimal200Carries
import BeaverStructural.BB6.Decimal200SumValues
import BeaverStructural.BB6.Decimal200SeedValues
import BeaverStructural.BB6.Decimal200EndpointValues

/-! Two hundred certified decimal digits of the original blank-input BB6 stop.

Every operand is the residue of an original counted source quantity. The seed,
two complete bulk phases, two resets, and final halt retain their original clock
weights. Finite residue-prefix certificates and proved stable tails evaluate the
astronomical tower expressions without evaluating the complete stopping integer.
The public theorem is about `exactN`, the same clock used by the original-machine
FirstHit theorem.
-/

namespace BeaverStructural.BB6.Decimal200
set_option compiler.extract_closed false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] tower towerSum towerSquareSum towerWeightedSum exhaustedWidth exhaustedRight stage1 stage2 bulkCost resetCost haltCost clockFor

private theorem right_to_tower (C : Counter) (m r : ℕ)
    (h : exhaustedRight C%m=r) : tower (C.count+1) C.base%m=r := by
  rw [← exhaustedRight]
  exact h

private theorem sum_value_transfer (f n m nr ar s : ℕ) (hn : n%m=nr) (ha : s=ar)
    (h : f%m=((n%m)*s)%m) : f%m=(nr*ar)%m := by rw [hn,ha] at h; exact h

private theorem square_value_transfer (f n m nr ar s : ℕ) (hn : n%m=nr) (ha : s=ar)
    (h : f%m=((n%m)*s^2)%m) : f%m=(nr*ar^2)%m := by rw [hn,ha] at h; exact h

private theorem weighted_value_transfer (f n m nr ar s : ℕ) (hn : n%m=nr) (ha : s=ar)
    (h : f%m=((n%m)*((n%m)+1)*s)%m) : f%m=(nr*(nr+1)*ar)%m := by rw [hn,ha] at h; exact h

theorem stage1_bulk_numeric : bulkCost stage1.count stage1.base%modulus=62577880240430482289368160298298912029448950783211106954399728175521557785415668260887366082536533747456267969089295451132160416678529032117666336793359881517034279228679331403488779244699220835302452 :=
  (ModularClock.bulkCode_correct modulus stage1.count stage1.base _ _ _ _ _ _ _
    (by decide) count1_numeric stage1_square_numeric stage1_linear_numeric
    (right_to_tower stage1 modulus _ stage1_right_numeric) stage1_first_numeric stage1_weighted_numeric carry1_numeric).trans (by decide +kernel)

theorem stage1_reset_numeric : resetCost stage1.length (exhaustedWidth stage1) (exhaustedRight stage1)%modulus=4815726901139646531375440357794357476412933291424850889656613249723028674997218758544776867394262501436329101111743465511192702866459685855505814681291134488050378309353642714463632845109273103959018 :=
  (ModularClock.resetCode_correct modulus stage1.length (exhaustedWidth stage1) (exhaustedRight stage1) _ _ _ _
    (by decide) length1_numeric width1_numeric stage1_right_numeric stage1_next_numeric).trans (by decide +kernel)

theorem stage2_linear_numeric : towerSum stage2.count (tower 2 stage2.base)%modulus=943847488230796558657791385665937201299537169067200330022478932493671067618966837311173925875083756519573077862508281082172593668997587294669663451481510099068110838469079843278040514600020840808449 :=
  change_modulus (towerSum stage2.count (tower 2 stage2.base)) 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 modulus _ rfl
    ((sum_value_transfer (towerSum stage2.count (tower 2 stage2.base)) stage2.count 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 _ _ _
      (change_modulus stage2.count modulus 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 _ rfl count2_numeric) steady_numeric
      (decimal.stage2_sum_residue decimal_stage2_depth 2 stage2.count)).trans (by decide +kernel))

theorem stage2_square_numeric : towerSquareSum stage2.count (tower 2 stage2.base)%modulus=54320346081358332817466608613945593138931868477497712966855434433051541509741798681748953778170494312747368883664852036270463131693880132584954065174592676576128042786998380986574099532045624146919423 :=
  change_modulus (towerSquareSum stage2.count (tower 2 stage2.base)) 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 modulus _ rfl
    ((square_value_transfer (towerSquareSum stage2.count (tower 2 stage2.base)) stage2.count 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 _ _ _
      (change_modulus stage2.count modulus 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 _ rfl count2_numeric) steady_numeric
      (decimal.stage2_square_residue decimal_stage2_depth 2 stage2.count)).trans (by decide +kernel))

theorem stage2_weighted_numeric : (2*towerWeightedSum stage2.count stage2.base)%modulus=96457810030035292682906154186204894826434750206529905806735518202111417290421299767562698095106799878996228783743431304056844253026294378640897250947290345633254062508894955253318559283738982232358912 :=
  change_modulus (2*towerWeightedSum stage2.count stage2.base) 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 modulus _ rfl
    ((weighted_value_transfer (2*towerWeightedSum stage2.count stage2.base) stage2.count 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 _ _ _
      (change_modulus stage2.count modulus 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 _ rfl count2_numeric) steady_numeric
      (decimal.stage2_weighted_residue decimal_stage2_depth stage2.count)).trans (by decide +kernel))

theorem stage2_bulk_numeric : bulkCost stage2.count stage2.base%modulus=99029225895553348173423862623031861494056283683955083230979086468565495661008702368470190776456140650047558954974374739715765530174934737242075893236756690566147363263377191150459575830874107246804012 :=
  (ModularClock.bulkCode_correct modulus stage2.count stage2.base _ _ _ _ _ _ _
    (by decide) count2_numeric stage2_square_numeric stage2_linear_numeric
    (stage2_tower_numeric (stage2.count+1)) (stage2_tower_numeric 1) stage2_weighted_numeric carry2_numeric).trans (by decide +kernel)

theorem stage2_halt_numeric : haltCost stage2.length (exhaustedWidth stage2)%modulus=65865066729976362022594573223630852625779762493974245896004180879014889668149541359117612809087723889725200149858126030831675820100040766178982750605246746391408933956654475589624401138199208877097976 :=
  (ModularClock.haltCode_correct modulus stage2.length (exhaustedWidth stage2) _ _ length2_numeric width2_numeric).trans (by decide +kernel)

theorem exactN_mod_decimal200 : exactN%modulus=76570746659301988709841908579693588126553130252541952029830709923036761639105158393970989783657593312221169567595808757858120886828361418774062055009809875683743490992412785802436230729390191074641105 := by
  rw [exactN_def]
  exact (ModularClock.clockCode_correct modulus seed stage1 stage2 _ _ _ _ _ _
    seed_bulk_numeric seed_reset_numeric stage1_bulk_numeric stage1_reset_numeric
    stage2_bulk_numeric stage2_halt_numeric).trans (by decide +kernel)

theorem exactN_mod_ten_pow_two_hundred : exactN%10^200=76570746659301988709841908579693588126553130252541952029830709923036761639105158393970989783657593312221169567595808757858120886828361418774062055009809875683743490992412785802436230729390191074641105 :=
  change_modulus exactN modulus (10^200) _ (by decide +kernel) exactN_mod_decimal200


end BeaverStructural.BB6.Decimal200
