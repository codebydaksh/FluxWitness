import FloatLibWorkspace.Binary64Law

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace heat_rounding_b64
noncomputable section

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat

theorem bpow_binary' (n : Int) :
    FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix n = (2 : Real) ^ n := by
  rfl

theorem eta_le_allowance : (2 : Real) ^ (-1075 : Int) <= 1 / 10 ^ 30 := by
  have h1 : FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix (-1075)
      <= FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix (-100) :=
    (FloatLib.Floats.Formats.Flocq.bpow_le_bpow_iff FloatLib.Numerics.binaryRadix
      (-1075) (-100)).mpr (by norm_num)
  rw [bpow_binary', bpow_binary'] at h1
  have h2 : (2 : Real) ^ (-100 : Int) <= 1 / 10 ^ 30 := by
    first
      | (norm_num; done)
      | (rw [zpow_neg]; norm_num; done)
  exact le_trans h1 h2

theorem binary64_bounded_round_law (x : Real) (hx : |x| <= 1000000) :
    |Model.roundAt binary64 x - x| <= (1 / 9007199254740992) * |x| + 1 / 10 ^ 30 := by
  have h := binary64_round_error_law x
  have hu : (2 : Real) ^ (-53 : Int) = 1 / 9007199254740992 := by norm_num
  rw [hu] at h
  linarith [h, eta_le_allowance]

end
end heat_rounding_b64

#print axioms heat_rounding_b64.binary64_bounded_round_law