import proofs.C1HalfSum

namespace heat_rounding
noncomputable section
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat

theorem c1_round_magnitude (x : Real) :
    |c1Arithmetic.round x| ≤ (1000001/1000000:Real)*|x| + 1/1000000 := by
  have he := c1Arithmetic.round_law x
  change |c1Arithmetic.round x-x| ≤ (1/9007199254740992:Real)*|x| + 1/10^30 at he
  have ht := abs_add_le (c1Arithmetic.round x-x) x
  rw [sub_add_cancel] at ht
  have hx := abs_nonneg x
  norm_num at he
  nlinarith

-- Derives the first-stage input condition needed by the second Euler call.
theorem c1_first_stage_bound (l c r dt : Real)
    (hl : |l| ≤ 2) (hc : |c| ≤ 2) (hr : |r| ≤ 2)
    (hdt : |dt| ≤ 9/2000) :
    |roundedEuler c1Arithmetic l c r dt storedD storedQ| ≤ 4 := by
  let a := c1Arithmetic
  let x1 := r-2*c
  let x2 := a.round x1+l
  let x3 := a.round x2/storedQ
  let x4 := storedD*a.round x3
  let x5 := dt*a.round x4
  let x6 := c+a.round x5
  have h1 : |x1| ≤ 6 := by
    have hb : |r-2*c| ≤ |r|+2*|c| := by
      calc
        |r-2*c| = |r + -(2*c)| := rfl
        _ ≤ |r|+|-(2*c)| := abs_add_le _ _
        _ = |r|+2*|c| := by
          rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0:Real)<2)]
    dsimp [x1]
    linarith
  have hr1 : |a.round x1| ≤ 6001/1000 := by
    have hb := c1_round_magnitude x1
    change |c1Arithmetic.round x1| ≤ 6001/1000
    linarith
  have h2 : |x2| ≤ 8001/1000 := by
    have hb := abs_add_le (a.round x1) l
    dsimp [x2]
    linarith
  have hr2 : |a.round x2| ≤ 4001/500 := by
    have hb := c1_round_magnitude x2
    change |c1Arithmetic.round x2| ≤ 4001/500
    linarith
  have hq : (1/5000:Real) ≤ storedQ := by norm_num [storedQ]
  have h3 : |x3| ≤ 40010 := by
    dsimp [x3]
    rw [abs_div, abs_of_pos storedQ_pos]
    apply (div_le_iff₀ storedQ_pos).mpr
    nlinarith
  have hr3 : |a.round x3| ≤ 40011 := by
    have hb := c1_round_magnitude x3
    change |c1Arithmetic.round x3| ≤ 40011
    linarith
  have hD : |storedD| ≤ (10001/1000000:Real) := by norm_num [storedD]
  have h4 : |x4| ≤ 401 := by
    have hb := mul_le_mul hD hr3 (abs_nonneg _) (by norm_num : (0:Real) ≤ 10001/1000000)
    dsimp [x4]
    rw [abs_mul]
    linarith
  have hr4 : |a.round x4| ≤ 402 := by
    have hb := c1_round_magnitude x4
    change |c1Arithmetic.round x4| ≤ 402
    linarith
  have h5 : |x5| ≤ 1809/1000 := by
    have hb := mul_le_mul hdt hr4 (abs_nonneg _) (by norm_num : (0:Real) ≤ 9/2000)
    dsimp [x5]
    rw [abs_mul]
    linarith
  have hr5 : |a.round x5| ≤ 181/100 := by
    have hb := c1_round_magnitude x5
    change |c1Arithmetic.round x5| ≤ 181/100
    linarith
  have h6 : |x6| ≤ 381/100 := by
    have hb := abs_add_le c (a.round x5)
    dsimp [x6]
    linarith
  have hb := c1_round_magnitude x6
  change |c1Arithmetic.round x6| ≤ 4
  linarith

theorem c1_euler_grid_representable (l c r dt : Real)
    (hl : |l| ≤ 4) (hc : |c| ≤ 4) (hr : |r| ≤ 4)
    (hdt : |dt| ≤ 9/2000) :
    Model.roundAt binary64 (roundedEuler c1Arithmetic l c r dt storedD storedQ) =
      roundedEuler c1Arithmetic l c r dt storedD storedQ := by
  rw [boundedEuler_eq_binary64_grid l c r dt hl hc hr hdt]
  unfold c1DirectEuler
  exact Model.roundAt_of_genericFormat binary64 (Model.genericFormat_roundAt binary64 _)

end
end heat_rounding
