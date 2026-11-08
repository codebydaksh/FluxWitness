import proofs.heat_rounding_certificate

/-! Extend arithmetic laws known only on a bounded operand domain to the
abstract LocalArithmetic interface. Outside that domain the extension uses
exact real arithmetic. It does not claim that native IEEE operations obey a
global no-overflow law. Native agreement still requires a domain proof at
every operation, and native bounded error laws remain separate obligations. -/
namespace heat_rounding
noncomputable section

def extendRound (B : Real) (native : Real → Real) (x : Real) : Real :=
  if |x| ≤ B then native x else x

def extendHalf (B : Real) (native : Real → Real) (x : Real) : Real :=
  if |x| ≤ B then native x else x/2

theorem extendRound_agrees (B : Real) (native : Real → Real) (x : Real)
    (hx : |x| ≤ B) : extendRound B native x = native x := by
  simp [extendRound, hx]

theorem extendHalf_agrees (B : Real) (native : Real → Real) (x : Real)
    (hx : |x| ≤ B) : extendHalf B native x = native x := by
  simp [extendHalf, hx]

theorem extendRound_law (B unit allowance : Real) (native : Real → Real)
    (hu : 0 ≤ unit) (he : 0 ≤ allowance)
    (hlaw : ∀ x, |x| ≤ B → |native x - x| ≤ unit * |x| + allowance) :
    ∀ x, |extendRound B native x - x| ≤ unit * |x| + allowance := by
  intro x
  by_cases hx : |x| ≤ B
  · simpa [extendRound, hx] using hlaw x hx
  · simp only [extendRound, if_neg hx, sub_self, abs_zero]
    exact add_nonneg (mul_nonneg hu (abs_nonneg x)) he

theorem extendHalf_law (B allowance : Real) (native : Real → Real)
    (he : 0 ≤ allowance)
    (hlaw : ∀ x, |x| ≤ B → |native x - x/2| ≤ allowance) :
    ∀ x, |extendHalf B native x - x/2| ≤ allowance := by
  intro x
  by_cases hx : |x| ≤ B
  · simpa [extendHalf, hx] using hlaw x hx
  · simpa [extendHalf, hx] using he

def arithmeticFromBoundedLaws (B unit allowance : Real)
    (nativeRound nativeHalf : Real → Real)
    (hu : 0 ≤ unit) (he : 0 ≤ allowance)
    (hr : ∀ x, |x| ≤ B → |nativeRound x-x| ≤ unit*|x|+allowance)
    (hh : ∀ x, |x| ≤ B → |nativeHalf x-x/2| ≤ allowance) : LocalArithmetic where
  unit := unit
  allowance := allowance
  unit_nonneg := hu
  round := extendRound B nativeRound
  round_law := extendRound_law B unit allowance nativeRound hu he hr
  half := extendHalf B nativeHalf
  half_law := extendHalf_law B allowance nativeHalf he hh

end
end heat_rounding
