import FloatLibWorkspace.Binary64Interface
import FloatLib.Floats.Formats.Flocq.Theory.Error.Multiplication

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace heat_rounding_b64
noncomputable section

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat

theorem b64_fracWidth : binary64.fracWidth = 52 := by
  first
    | rfl
    | decide

theorem b64_minSub : binary64.minSubnormalExponent = -1074 := by
  first
    | rfl
    | decide
    | (simp [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent]; done)

theorem two_zpow_le (a b : Int) (hab : a <= b) : (2 : Real) ^ a <= (2 : Real) ^ b := by
  have h := (FloatLib.Floats.Formats.Flocq.bpow_le_bpow_iff
    FloatLib.Numerics.binaryRadix a b).mpr hab
  rw [bpow_binary', bpow_binary'] at h
  exact h

def nativeHalf (x : Real) : Real := by
  classical
  exact if Model.roundAt binary64 x = x then Model.roundAt binary64 (x / 2) else x / 2

theorem half_small (x : Real) (hs : |x| < (2 : Real) ^ (-1021 : Int)) :
    |Model.roundAt binary64 (x / 2) - x / 2| <= 1 / 10 ^ 30 := by
  have h := binary64_round_error_law (x / 2)
  have habs : |x / 2| = |x| / 2 := by rw [abs_div, abs_two]
  have h1 : (2 : Real) ^ (-1021 : Int) <= (2 : Real) ^ (-110 : Int) :=
    two_zpow_le _ _ (by norm_num)
  have h2 : (2 : Real) ^ (-1075 : Int) <= (2 : Real) ^ (-110 : Int) :=
    two_zpow_le _ _ (by norm_num)
  have h3 : (2 : Real) ^ (-53 : Int) <= 1 := by norm_num
  have h4 : (2 : Real) ^ (-53 : Int) * |x / 2| <= |x / 2| :=
    mul_le_of_le_one_left (abs_nonneg _) h3
  have h5 : (2 : Real) ^ (-110 : Int) + (2 : Real) ^ (-110 : Int) <= 1 / 10 ^ 30 := by
    first
      | (norm_num; done)
      | (rw [zpow_neg]; norm_num; done)
  have hx2 : |x / 2| <= (2 : Real) ^ (-110 : Int) := by
    rw [habs]
    exact le_trans (half_le_self (abs_nonneg x)) (le_trans (le_of_lt hs) h1)
  exact le_trans h (le_trans (add_le_add h4 (le_refl _)) (le_trans (add_le_add hx2 h2) h5))

theorem half_exact (x : Real) (hrep : Model.roundAt binary64 x = x)
    (hbig : (2 : Real) ^ (-1021 : Int) <= |x|) :
    Model.roundAt binary64 (x / 2) = x / 2 := by
  have hx0 : Ne x 0 := by
    intro h0
    rw [h0, abs_zero] at hbig
    have hp : (0 : Real) < (2 : Real) ^ (-1021 : Int) := by positivity
    exact absurd hbig (not_le.mpr hp)
  have hg : FloatLib.Floats.Formats.Flocq.genericFormat FloatLib.Numerics.binaryRadix
      (Model.fexpOf binary64) x := by
    have h := Model.genericFormat_roundAt binary64 x
    rw [hrep] at h
    exact h
  have hmag : (-1020 : Int) <= FloatLib.Floats.Formats.Flocq.magnitude
      FloatLib.Numerics.binaryRadix x := by
    have h1 := FloatLib.Floats.Formats.Flocq.abs_lt_bpow_magnitude
      FloatLib.Numerics.binaryRadix x hx0
    have h2 : FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix (-1021)
        <= |x| := by
      rw [bpow_binary']
      exact hbig
    have h3 := lt_of_le_of_lt h2 h1
    have h4 := (FloatLib.Floats.Formats.Flocq.bpow_lt_bpow_iff FloatLib.Numerics.binaryRadix
      (-1021) (FloatLib.Floats.Formats.Flocq.magnitude FloatLib.Numerics.binaryRadix x)).mp h3
    omega
  have hshift : binary64.minSubnormalExponent + ((binary64.fracWidth : Int) + 1)
      - FloatLib.Floats.Formats.Flocq.magnitude FloatLib.Numerics.binaryRadix x <= -1 := by
    have e1 := b64_minSub
    have e2 := b64_fracWidth
    omega
  have hmul := FloatLib.Floats.Formats.Flocq.generic_format_FLT_mul_bpow
    binary64.minSubnormalExponent ((binary64.fracWidth : Int) + 1) (by positivity)
    hg (-1) hshift
  have hval : x * FloatLib.Floats.Formats.Flocq.bpow FloatLib.Numerics.binaryRadix (-1)
      = x / 2 := by
    rw [bpow_binary', zpow_neg_one]
    ring
  rw [hval] at hmul
  exact Model.roundAt_of_genericFormat binary64 hmul

theorem binary64_half_law (x : Real) (hx : |x| <= 1000000) :
    |nativeHalf x - x / 2| <= 1 / 10 ^ 30 := by
  unfold nativeHalf
  by_cases hrep : Model.roundAt binary64 x = x
  . rw [if_pos hrep]
    by_cases hbig : (2 : Real) ^ (-1021 : Int) <= |x|
    . rw [half_exact x hrep hbig, sub_self, abs_zero]
      positivity
    . exact half_small x (not_le.mp hbig)
  . rw [if_neg hrep, sub_self, abs_zero]
    positivity

end
end heat_rounding_b64

#print axioms heat_rounding_b64.binary64_half_law