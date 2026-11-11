import BeaverStructural.BB6.Decimal200PeriodRows9
import BeaverStructural.BB6.Decimal200SteadyValues
import BeaverStructural.BB6.Decimal200LiteralSums

/-! Exact shared residue prefix for the decimal modulus, built from the checked
child-period row. All entries are used by the original tower-sum formulas. -/
namespace BeaverStructural.BB6.Decimal200
set_option compiler.extract_closed false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000


theorem decimalRow_correct : TowerModulus.residuePrefix decimal=decimalRow := by
  unfold decimal
  rewrite [TowerModulus.prefix_step,periodRow199_correct]
  have h : periodRow199=decimalParentRow := by decide +kernel
  rw [h]
  exact decimal_top_row_code

theorem decimal_depth_numeric : decimal.depth=201 := by decide +kernel


theorem decimalResidueValue_correct (h : ℕ) : decimal.residue h=decimalResidueValue h := by
  unfold decimalResidueValue
  split_ifs with hh
  · have hp : h<decimal.residuePrefix.length := by rw [decimalRow_correct]; exact hh
    have he := decimal.prefix_getElem h hp
    simpa only [decimalRow_correct] using he.symm
  · have hl : decimalRow.length=204 := by decide +kernel
    have hd : decimal.depth+2≤h := by rewrite [decimal_depth_numeric]; omega
    exact (decimal.residue_correct h).symm.trans
      ((decimal.steady_correct h hd).trans steady_numeric)

theorem decimal_prefix8_sum :
    (∑ i ∈ Finset.range (decimal.depth+2), decimal.residue (8+i))=10519035017814814149019757396213511235402242411180172813394016503881046705985823219427604446745766777340740326876382001657465221586147917658909846952222301946960881368846061898683860068268807022427766581 := by
  rewrite [decimal_depth_numeric]
  have he : (∑ i ∈ Finset.range 203, decimal.residue (8+i))=
      (∑ i ∈ Finset.range 203, decimalResidueValue (8+i)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact decimalResidueValue_correct (8+i)
  exact he.trans decimal_prefix8_literal

end BeaverStructural.BB6.Decimal200
