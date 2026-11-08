import proofs.heat_rounding_evolution
import proofs.heat_bounded_arithmetic
import FloatLibWorkspace.Binary64Half

/-! Candidate operand-domain proof for the stored-parameter Euler expression.
This does not identify round with binary64. It bounds each argument supplied
to round, so a bounded-domain native interpretation has explicit targets.
The input bound 4 covers the intermediate stages once their separate stage
bound is applied. No native or driver theorem is claimed here. -/
namespace heat_rounding
noncomputable section

theorem round_magnitude_of_unit_le_one (a : LocalArithmetic)
    (hu : a.unit ≤ 1) (he : a.allowance ≤ 1) (x : Real) :
    |a.round x| ≤ 2*|x|+1 := by
  have ht : |a.round x| ≤ |a.round x-x|+|x| := by
    calc
      |a.round x| = |(a.round x-x)+x| := by rw [sub_add_cancel]
      _ ≤ |a.round x-x|+|x| := abs_add_le _ _
  have hm := mul_le_mul_of_nonneg_right hu (abs_nonneg x)
  have hr := a.round_law x
  nlinarith

def EulerOperandDomain (a : LocalArithmetic) (l c r dt : Real) (B : Real) : Prop :=
  let x1 := r-2*c
  let x2 := a.round x1+l
  let x3 := a.round x2/storedQ
  let x4 := storedD*a.round x3
  let x5 := dt*a.round x4
  let x6 := c+a.round x5
  |x1| ≤ B ∧ |x2| ≤ B ∧ |x3| ≤ B ∧ |x4| ≤ B ∧ |x5| ≤ B ∧ |x6| ≤ B

theorem storedEuler_operand_domain (a : LocalArithmetic)
    (hu : a.unit ≤ 1) (he : a.allowance ≤ 1)
    (l c r dt : Real) (hl : |l| ≤ 4) (hc : |c| ≤ 4) (hr : |r| ≤ 4)
    (hdt : |dt| ≤ 9/2000) :
    EulerOperandDomain a l c r dt 1000000 ∧
    |roundedEuler a l c r dt storedD storedQ| ≤ 487 := by
  let x1 := r-2*c
  let x2 := a.round x1+l
  let x3 := a.round x2/storedQ
  let x4 := storedD*a.round x3
  let x5 := dt*a.round x4
  let x6 := c+a.round x5
  have rounding := round_magnitude_of_unit_le_one a hu he
  have h1 : |x1| ≤ 12 := by
    have hb : |r-2*c| ≤ |r|+2*|c| := by
      calc
        |r-2*c| = |r + -(2*c)| := rfl
        _ ≤ |r|+|-(2*c)| := abs_add_le _ _
        _ = |r|+2*|c| := by
          rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0:Real)<2)]
    dsimp [x1]
    linarith
  have h2 : |x2| ≤ 29 := by
    have hb := abs_add_le (a.round x1) l
    have hd := rounding x1
    dsimp [x2]
    linarith
  have hq : (1/5000:Real) ≤ storedQ := by norm_num [storedQ]
  have h3 : |x3| ≤ 295000 := by
    have hb := rounding x2
    dsimp [x3]
    rw [abs_div, abs_of_pos storedQ_pos]
    apply (div_le_iff₀ storedQ_pos).mpr
    nlinarith
  have hD : |storedD| ≤ (1/50:Real) := by norm_num [storedD]
  have h4 : |x4| ≤ 11801 := by
    have hb := rounding x3
    have hm := mul_le_mul hD (show |a.round x3| ≤ 590001 by linarith)
      (abs_nonneg _) (by norm_num : (0:Real) ≤ 1/50)
    dsimp [x4]
    rw [abs_mul]
    linarith
  have h5 : |x5| ≤ 119 := by
    have hb := rounding x4
    have hm := mul_le_mul (show |dt| ≤ (1/200:Real) by linarith)
      (show |a.round x4| ≤ 23603 by linarith) (abs_nonneg _)
      (by norm_num : (0:Real) ≤ 1/200)
    dsimp [x5]
    rw [abs_mul]
    linarith
  have h6 : |x6| ≤ 243 := by
    have hb := abs_add_le c (a.round x5)
    have hd := rounding x5
    dsimp [x6]
    linarith
  constructor
  · change |x1| ≤ 1000000 ∧ |x2| ≤ 1000000 ∧ |x3| ≤ 1000000 ∧
      |x4| ≤ 1000000 ∧ |x5| ≤ 1000000 ∧ |x6| ≤ 1000000
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · change |a.round x6| ≤ 487
    have hb := rounding x6
    linarith

end
end heat_rounding



/- C1 gate: removes the bounded-extension switch for one Euler expression.
   This is not a C execution theorem. The direct expression retains exact
   doubling; identification with C's rounded 2.0*c needs its own proof.
   No finiteness or representability premise is silently discharged here. -/
namespace heat_rounding
noncomputable section

def c1DirectEuler (R : Real → Real) (l c r dt : Real) : Real :=
  R (c + R (dt * R (storedD * R (R (R (r - 2*c) + l) / storedQ))))

theorem storedEuler_eq_direct_of_domain (a : LocalArithmetic)
    (R : Real → Real)
    (hagrees : ∀ x, |x| ≤ 1000000 → a.round x = R x)
    (l c r dt : Real)
    (hdom : EulerOperandDomain a l c r dt 1000000) :
    roundedEuler a l c r dt storedD storedQ = c1DirectEuler R l c r dt := by
  rcases hdom with ⟨h1, h2, h3, h4, h5, h6⟩
  have e1 := hagrees (r - 2*c) h1
  have e2 := hagrees (a.round (r - 2*c) + l) h2
  have e3 := hagrees (a.round (a.round (r - 2*c) + l) / storedQ) h3
  have e4 := hagrees
    (storedD * a.round (a.round (a.round (r - 2*c) + l) / storedQ)) h4
  have e5 := hagrees
    (dt * a.round (storedD * a.round (a.round (a.round (r - 2*c) + l) / storedQ))) h5
  have e6 := hagrees
    (c + a.round (dt * a.round (storedD * a.round
      (a.round (a.round (r - 2*c) + l) / storedQ)))) h6
  unfold roundedEuler roundedStencil c1DirectEuler
  rw [e6, e5, e4, e3, e2, e1]

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat

-- Same arithmetic parameters and laws as the accepted combined benchmark.
def c1Arithmetic : LocalArithmetic :=
  arithmeticFromBoundedLaws 1000000 (1/9007199254740992) (1/10^30)
    (Model.roundAt binary64) heat_rounding_b64.nativeHalf
    (by norm_num) (by norm_num)
    heat_rounding_b64.binary64_bounded_round_law heat_rounding_b64.binary64_half_law

theorem boundedEuler_eq_binary64_grid (l c r dt : Real)
    (hl : |l| ≤ 4) (hc : |c| ≤ 4) (hr : |r| ≤ 4)
    (hdt : |dt| ≤ 9/2000) :
    roundedEuler c1Arithmetic l c r dt storedD storedQ =
      c1DirectEuler (Model.roundAt binary64) l c r dt := by
  have hu : c1Arithmetic.unit ≤ 1 := by
    norm_num [c1Arithmetic, arithmeticFromBoundedLaws]
  have he : c1Arithmetic.allowance ≤ 1 := by
    norm_num [c1Arithmetic, arithmeticFromBoundedLaws]
  have hdomain := (storedEuler_operand_domain c1Arithmetic hu he
    l c r dt hl hc hr hdt).1
  apply storedEuler_eq_direct_of_domain c1Arithmetic (Model.roundAt binary64)
    _ l c r dt hdomain
  intro x hx
  exact extendRound_agrees 1000000 (Model.roundAt binary64) x hx

end
end heat_rounding
