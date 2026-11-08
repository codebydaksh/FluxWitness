import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-! Sharp scalar Taylor remainder bounds for the heat local-defect proof.
The polynomial here is Mathlib's within-interval Taylor polynomial. Connecting
its coefficients to PDE derivatives is a separate obligation. -/
namespace heat_taylor
open Set

theorem scalar_remainder_bound (f : Real → Real) (a x M : Real) (n : Nat)
    (hf : ContDiffOn Real (n+1) f (uIcc a x))
    (hM : ∀ y ∈ uIoo a x, |iteratedDeriv (n+1) f y| ≤ M) :
    |f x - taylorWithinEval f n (uIcc a x) a x| ≤
      M * |x-a|^(n+1) / (n+1).factorial := by
  by_cases hax : a = x
  · subst x
    simp [taylorWithinEval_self]
  · obtain ⟨y, hy, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hax hf
    rw [heq, abs_div, abs_mul, abs_pow, Nat.abs_cast]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hM y hy) (pow_nonneg (abs_nonneg _) _))
      (Nat.cast_nonneg _)

/-- Cubic time remainder with its factorial constant, before substituting the PDE. -/
theorem quadratic_remainder_bound (f : Real → Real) (a x M : Real)
    (hf : ContDiffOn Real 3 f (uIcc a x))
    (hM : ∀ y ∈ uIoo a x, |iteratedDeriv 3 f y| ≤ M) :
    |f x - taylorWithinEval f 2 (uIcc a x) a x| ≤ M * |x-a|^3 / 6 := by
  convert scalar_remainder_bound f a x M 2 hf hM using 1 <;> norm_num

end heat_taylor
#print axioms heat_taylor.scalar_remainder_bound
#print axioms heat_taylor.quadratic_remainder_bound
