import BeaverStructural.BB6.FirstHit
import BeaverStructural.BB6.Decimal200Certificate
import BeaverStructural.BB7.Sigma
import BeaverStructural.BB7.DigitsFinal
import BeaverStructural.BB7b.Run
import BeaverStructural.BB7b.DigitsVals
import BeaverStructural.BB34.Run
import BeaverStructural.BB34.DigitsFinal

/-! One statement per machine: from the blank tape the machine stops first at exactly its step count, and the last
200 decimal digits of that count (and of the score) are the literals. -/

namespace BeaverStructural

/-- BB(6), `1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE`: the first stop is at `BB6.exactN`. -/
theorem bb6_first_stop_and_digits :
    FirstHit BB6.table BB6.exactN BB6.blank ∧
    BB6.exactN % 10 ^ 200 = 76570746659301988709841908579693588126553130252541952029830709923036761639105158393970989783657593312221169567595808757858120886828361418774062055009809875683743490992412785802436230729390191074641105 :=
  ⟨BB6.first_hit_exact, BB6.Decimal200.exactN_mod_ten_pow_two_hundred⟩

/-- BB(7), `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF`: the first stop is at `BB7.tau`, and the halted tape
holds `BB7.sigma` ones. -/
theorem bb7_first_stop_and_digits :
    (((step BB7.table)^[BB7.tau] BB7.blank).state = none ∧
      ∀ t < BB7.tau, ((step BB7.table)^[t] BB7.blank).state ≠ none) ∧
    Set.ncard {p : ℤ | ((step BB7.table)^[BB7.tau] BB7.blank).tape p = true} = BB7.sigma ∧
    BB7.tau % 10 ^ 200 = 10442722074196456773707640344163283107608038313650144315814389328319446910761894323931867085376411580682445199494700647587803129645200041753088294078160945237875590633254874041202959286480341950034543 ∧
    BB7.sigma % 10 ^ 200 = 12897809075781567187510870723274308261486089663242393885290451904435315345520726377730964080560052153267706661570675282053969566167812736363848524885873710436586090617800479560014295845226060298846230 :=
  ⟨BB7.champion_first_stop, BB7.champion_sigma, BB7.tau_mod_ten200, BB7.sigma_mod_ten200⟩

/-- BB(7), `1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB`: the first stop is at `BB7b.tau`, and the halted tape
is that of a zipper holding `BB7b.sigma` ones. -/
theorem bb7b_first_stop_and_digits :
    (((step BB7b.table)^[BB7b.tau] BB7b.blank).state = none ∧
      ∀ t < BB7b.tau, ((step BB7b.table)^[t] BB7b.blank).state ≠ none) ∧
    (∃ z : BB7b.Zip, ((step BB7b.table)^[BB7b.tau] BB7b.blank) = z.config ∧
      z.left.count true + z.right.count true = BB7b.sigma) ∧
    BB7b.tau % 10 ^ 200 = 73428777837952993932558769478822530186098574054291312567353699908846487228941494006822946829647472038108444008989374401252315208961679286188413869309976773701212302531357930057713528229743458345356287 ∧
    BB7b.sigma % 10 ^ 200 = 38146269853501365410645620969226103723067399102116242894037345432144851507307992961694105209402589140584375632186552499340414462252588919319066067278807809867872153028729243567821670670118939603706013 :=
  ⟨BB7b.machine_first_stop, BB7b.machine_sigma, BB7b.tau_mod_ten200, BB7b.sigma_mod_ten200⟩

/-- BB(3,4), `1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC`: the first stop is at `BB34.tau`, and the halted tape is that
of a zipper holding `BB34.sigma` nonblank cells. -/
theorem bb34_first_stop_and_digits :
    (((BB34.step BB34.table)^[BB34.tau] BB34.blank).state = none ∧
      ∀ t < BB34.tau, ((BB34.step BB34.table)^[t] BB34.blank).state ≠ none) ∧
    (∃ z : BB34.Zip, ((BB34.step BB34.table)^[BB34.tau] BB34.blank) = z.config ∧
      BB34.nb z.left + BB34.nb z.right = BB34.sigma) ∧
    BB34.tau % 10 ^ 200 = 66472556816678537004442489651861394493871801061408453005565013967672312146603676135321084747442383169401224698960399961853900728282682573633487960377917913767778012157999678639877282968144064457604929 ∧
    BB34.sigma % 10 ^ 200 = 4299269691927189062503623574424769420495363221080797961763483968145105115173575459243654693520017384422568887190225094017989855389270912121282841628624570145528696872600159853338098615075353432948750 :=
  ⟨BB34.machine_first_stop, BB34.machine_sigma, BB34.tau_mod_ten200, BB34.sigma_mod_ten200⟩

end BeaverStructural

#print axioms BeaverStructural.bb6_first_stop_and_digits
#print axioms BeaverStructural.bb7_first_stop_and_digits
#print axioms BeaverStructural.bb7b_first_stop_and_digits
#print axioms BeaverStructural.bb34_first_stop_and_digits
