import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Identification of within-set Taylor coefficients with ordinary derivatives.
Unique differentiability and differentiability at the expansion point are explicit.
These identities connect the analytic remainder theorem to PDE derivative formulas. -/
namespace heat_taylor_coefficients
open Set

theorem quadratic (f : Real → Real) (s : Set Real) (a x : Real)
    (hs : UniqueDiffOn Real s) (ha : a ∈ s) (hf : ContDiffAt Real 2 f a) :
    taylorWithinEval f 2 s a x =
      f a + (x-a) * deriv f a + (x-a)^2 / 2 * iteratedDeriv 2 f a := by
  have h1 : iteratedDerivWithin 1 f s a = deriv f a := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs (hf.of_le (by norm_num)) ha]
    rw [iteratedDeriv_one]
  have h2 : iteratedDerivWithin 2 f s a = iteratedDeriv 2 f a :=
    iteratedDerivWithin_eq_iteratedDeriv hs hf ha
  norm_num [taylorWithinEval_succ, taylor_within_zero_eval, h1, h2, smul_eq_mul]
  <;> ring_nf <;> simp

theorem cubic (f : Real → Real) (s : Set Real) (a x : Real)
    (hs : UniqueDiffOn Real s) (ha : a ∈ s) (hf : ContDiffAt Real 3 f a) :
    taylorWithinEval f 3 s a x =
      f a + (x-a) * deriv f a + (x-a)^2 / 2 * iteratedDeriv 2 f a +
      (x-a)^3 / 6 * iteratedDeriv 3 f a := by
  have h2 := quadratic f s a x hs ha (hf.of_le (by norm_num))
  have h3 : iteratedDerivWithin 3 f s a = iteratedDeriv 3 f a :=
    iteratedDerivWithin_eq_iteratedDeriv hs hf ha
  rw [show (3 : Nat) = 2+1 from rfl, taylorWithinEval_succ, h2]
  norm_num [h3, smul_eq_mul]
  <;> ring_nf <;> simp

end heat_taylor_coefficients
#print axioms heat_taylor_coefficients.quadratic
#print axioms heat_taylor_coefficients.cubic

