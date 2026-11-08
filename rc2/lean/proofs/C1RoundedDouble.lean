import proofs.C1EulerAgreement
import FloatLib.Floats.Formats.Flocq.Theory.Error.Multiplication

namespace heat_rounding
noncomputable section
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat

-- Mathematical grid exactness. This is not a hardware no-overflow theorem.
theorem c1_double_grid_exact (x : Real)
    (hrep : Model.roundAt binary64 x = x) :
    Model.roundAt binary64 (2*x) = 2*x := by
  have hg := Model.genericFormat_roundAt binary64 x
  rw [hrep] at hg
  have hm := FloatLib.Floats.Formats.Flocq.generic_format_FLT_mul_bpow_of_nonneg
    (β := FloatLib.Numerics.binaryRadix)
    binary64.minSubnormalExponent ((binary64.fracWidth : Int) + 1)
    (by positivity) hg 1 (by norm_num)
  rw [heat_rounding_b64.bpow_binary'] at hm
  simp only [zpow_one] at hm
  have heq := Model.roundAt_of_genericFormat binary64 hm
  simpa only [mul_comm] using heq

-- Explicit grid-rounding at the doubling, then the original subtraction,
-- left-neighbor addition, division, diffusivity multiply and Euler operations.
def c1ExplicitRoundedEuler (l c r dt : Real) : Real :=
  let R := Model.roundAt binary64
  R (c + R (dt * R (storedD * R (R (R (r - R (2*c)) + l) / storedQ))))

theorem c1_explicitEuler_eq_direct (l c r dt : Real)
    (hcRep : Model.roundAt binary64 c = c) :
    c1ExplicitRoundedEuler l c r dt =
      c1DirectEuler (Model.roundAt binary64) l c r dt := by
  dsimp only [c1ExplicitRoundedEuler, c1DirectEuler]
  rw [c1_double_grid_exact c hcRep]

theorem boundedEuler_eq_explicit_rounded (l c r dt : Real)
    (hl : |l| ≤ 4) (hc : |c| ≤ 4) (hr : |r| ≤ 4)
    (hdt : |dt| ≤ 9/2000)
    (hcRep : Model.roundAt binary64 c = c) :
    roundedEuler c1Arithmetic l c r dt storedD storedQ =
      c1ExplicitRoundedEuler l c r dt := by
  rw [boundedEuler_eq_binary64_grid l c r dt hl hc hr hdt,
      c1_explicitEuler_eq_direct l c r dt hcRep]

end
end heat_rounding
