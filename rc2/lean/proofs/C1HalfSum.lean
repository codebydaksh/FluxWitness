import proofs.C1RoundedDouble

namespace heat_rounding
noncomputable section
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat

theorem c1_nativeHalf_eq_grid (x : Real)
    (hrep : Model.roundAt binary64 x = x) :
    heat_rounding_b64.nativeHalf x = Model.roundAt binary64 (x/2) := by
  simp only [heat_rounding_b64.nativeHalf, if_pos hrep]

theorem c1_nativeHalf_magnitude (x : Real) (hx : |x| ≤ 1000000) :
    |heat_rounding_b64.nativeHalf x| ≤ |x|/2 + 1 := by
  have he := heat_rounding_b64.binary64_half_law x hx
  have ht := abs_add_le (heat_rounding_b64.nativeHalf x-x/2) (x/2)
  rw [sub_add_cancel] at ht
  rw [abs_div, abs_of_pos (by norm_num : (0:Real)<2)] at ht
  have heps : (1/10^30 : Real) ≤ 1 := by norm_num
  linarith

-- The operand bounds here are explicit premises, not a proof of stage reachability.
theorem boundedHalfSum_eq_explicit_rounded (u t : Real)
    (hu : |u| ≤ 2) (ht : |t| ≤ 487)
    (huRep : Model.roundAt binary64 u = u)
    (htRep : Model.roundAt binary64 t = t) :
    c1Arithmetic.round (c1Arithmetic.half u + c1Arithmetic.half t) =
      Model.roundAt binary64
        (Model.roundAt binary64 (u/2) + Model.roundAt binary64 (t/2)) := by
  have huDomain : |u| ≤ 1000000 := by linarith
  have htDomain : |t| ≤ 1000000 := by linarith
  have hmu := c1_nativeHalf_magnitude u huDomain
  have hmt := c1_nativeHalf_magnitude t htDomain
  have hsum : |heat_rounding_b64.nativeHalf u + heat_rounding_b64.nativeHalf t| ≤ 1000000 := by
    have hs := abs_add_le (heat_rounding_b64.nativeHalf u) (heat_rounding_b64.nativeHalf t)
    linarith
  have eu : c1Arithmetic.half u = heat_rounding_b64.nativeHalf u :=
    extendHalf_agrees 1000000 heat_rounding_b64.nativeHalf u huDomain
  have et : c1Arithmetic.half t = heat_rounding_b64.nativeHalf t :=
    extendHalf_agrees 1000000 heat_rounding_b64.nativeHalf t htDomain
  rw [eu, et]
  have es : c1Arithmetic.round
      (heat_rounding_b64.nativeHalf u + heat_rounding_b64.nativeHalf t) =
      Model.roundAt binary64
        (heat_rounding_b64.nativeHalf u + heat_rounding_b64.nativeHalf t) :=
    extendRound_agrees 1000000 (Model.roundAt binary64) _ hsum
  rw [es, c1_nativeHalf_eq_grid u huRep, c1_nativeHalf_eq_grid t htRep]

end
end heat_rounding
