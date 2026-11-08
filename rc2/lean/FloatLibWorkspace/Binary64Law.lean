import FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace heat_rounding_b64
noncomputable section

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat

theorem binary64_round_error_law (x : Real) :
    |Model.roundAt binary64 x - x|
      <= (2 : Real) ^ (-53 : Int) * |x| + (2 : Real) ^ (-1075 : Int) := by
  obtain ⟨ d, e, h, hd, he, hde ⟩ := Model.roundAt_standardModel binary64 x
  have hfw : binary64.fracWidth = 52 := by
    first
      | rfl
      | decide
  have hu : Model.unitRoundoffAt binary64 = (2 : Real) ^ (-53 : Int) := by
    rw [Model.unitRoundoffAt_eq]
    first
      | (rw [hfw]; norm_num; done)
      | (norm_num [hfw]; done)
  have hms : binary64.minSubnormalExponent = -1074 := by
    first
      | rfl
      | decide
      | (simp [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent]; done)
  have hv : Model.underflowErrorAt binary64 = (2 : Real) ^ (-1075 : Int) := by
    rw [Model.underflowErrorAt_eq, hms, show (-1074 - 1 : Int) = -1075 by norm_num]
  rw [hu] at hd
  rw [hv] at he
  have hsub : Model.roundAt binary64 x - x = x * d + e := by
    rw [h]; ring
  have h1 : |x * d + e| <= |x * d| + |e| := by
    first
      | exact abs_add _ _
      | exact abs_add_le _ _
  have h2 : |x * d| = |x| * |d| := abs_mul x d
  have h3 : |x| * |d| <= (2 : Real) ^ (-53 : Int) * |x| := by
    calc |x| * |d| <= |x| * (2 : Real) ^ (-53 : Int) :=
          mul_le_mul_of_nonneg_left hd (abs_nonneg x)
      _ = (2 : Real) ^ (-53 : Int) * |x| := mul_comm _ _
  rw [hsub]
  linarith [h1, h2, h3, he]

end
end heat_rounding_b64

#print axioms heat_rounding_b64.binary64_round_error_law