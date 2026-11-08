import proofs.heat_taylor
import proofs.heat_taylor_coefficients
import proofs.heat_stencil_error
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! Analytic connection from smoothness and derivative bounds to the stencil.
Candidate awaiting compilation; no installation or verification claim. -/
namespace heat_consistency_bridge
open Set

/-- Ordinary-derivative cubic Taylor bound, derived rather than assumed.
Global C4 smoothness is a sufficient regularity hypothesis; the derivative bound
is required only between the two evaluation points. -/
theorem cubic_error (f : Real → Real) (a x M : Real)
    (hax : a ≠ x) (hf : ContDiff Real 4 f)
    (hM : ∀ y ∈ uIoo a x, |iteratedDeriv 4 f y| ≤ M) :
    |f x - (f a + (x-a)*deriv f a + (x-a)^2/2*iteratedDeriv 2 f a +
      (x-a)^3/6*iteratedDeriv 3 f a)| ≤ M*|x-a|^4/24 := by
  have hs : UniqueDiffOn Real (uIcc a x) := by
    rcases lt_or_gt_of_ne hax with h | h
    · rw [uIcc_of_le (le_of_lt h)]
      exact uniqueDiffOn_Icc h
    · rw [uIcc_of_ge (le_of_lt h)]
      exact uniqueDiffOn_Icc h
  have ha : a ∈ uIcc a x := left_mem_uIcc
  have hc := heat_taylor_coefficients.cubic f (uIcc a x) a x hs ha
    (hf.contDiffAt.of_le (by norm_num))
  have hr := heat_taylor.scalar_remainder_bound f a x M 3 hf.contDiffOn hM
  rw [hc] at hr
  convert hr using 1 <;> norm_num

/-- Spatial consistency with explicit fourth-derivative regularity and bound.
The two Taylor remainder premises of the algebraic stencil lemma are discharged. -/
theorem centered_consistency (f : Real → Real) (a h M : Real)
    (hh : 0 < h) (hf : ContDiff Real 4 f)
    (hM : ∀ y, |iteratedDeriv 4 f y| ≤ M) :
    |(f (a+h) - 2*f a + f (a-h))/h^2 - iteratedDeriv 2 f a| ≤ M*h^2/12 := by
  have hp := cubic_error f a (a+h) M (by linarith) hf (fun y _ => hM y)
  have hm := cubic_error f a (a-h) M (by linarith) hf (fun y _ => hM y)
  rw [show a+h-a=h by ring, abs_of_pos hh] at hp
  rw [show a-h-a= -h by ring, abs_neg, abs_of_pos hh] at hm
  have heq : f a + (-h)*deriv f a + (-h)^2/2*iteratedDeriv 2 f a +
      (-h)^3/6*iteratedDeriv 3 f a =
      f a - h*deriv f a + h^2/2*iteratedDeriv 2 f a - h^3/6*iteratedDeriv 3 f a := by ring
  rw [heq] at hm
  exact heat_stencil_error.centered_from_cubic_remainders
    (f (a-h)) (f a) (f (a+h)) (deriv f a) (iteratedDeriv 2 f a)
    (iteratedDeriv 3 f a) h M hh hp hm
/-- Time consistency for a nonnegative time increment. The bound on g''' is
explicit; a PDE application must derive it from the equation and spatial bounds. -/
theorem time_quadratic_error (g : Real → Real) (t dt M : Real)
    (hdt : 0 ≤ dt) (hg : ContDiff Real 3 g)
    (hM : ∀ y ∈ uIoo t (t+dt), |iteratedDeriv 3 g y| ≤ M) :
    |g (t+dt) - (g t + dt*deriv g t + dt^2/2*iteratedDeriv 2 g t)| ≤ M*dt^3/6 := by
  by_cases hz : dt = 0
  · subst dt
    simp
  · have hp : 0 < dt := lt_of_le_of_ne hdt (Ne.symm hz)
    have hs : UniqueDiffOn Real (uIcc t (t+dt)) := by
      rw [uIcc_of_le (by linarith)]
      exact uniqueDiffOn_Icc (by linarith)
    have hc := heat_taylor_coefficients.quadratic g (uIcc t (t+dt)) t (t+dt)
      hs left_mem_uIcc (hg.contDiffAt.of_le (by norm_num))
    have hr := heat_taylor.quadratic_remainder_bound g t (t+dt) M hg.contDiffOn hM
    rw [hc, show t+dt-t=dt by ring, abs_of_nonneg hdt] at hr
    exact hr
 theorem linear_error (f : Real → Real) (a x B : Real)
    (hax : a ≠ x) (hf : ContDiff Real 2 f)
    (hB : ∀ y ∈ uIoo a x, |iteratedDeriv 2 f y| ≤ B) :
    |f x - (f a + (x-a)*deriv f a)| ≤ B*|x-a|^2/2 := by
  have hs : UniqueDiffOn Real (uIcc a x) := by
    rcases lt_or_gt_of_ne hax with h | h
    · rw [uIcc_of_le (le_of_lt h)]
      exact uniqueDiffOn_Icc h
    · rw [uIcc_of_ge (le_of_lt h)]
      exact uniqueDiffOn_Icc h
  have h1 : iteratedDerivWithin 1 f (uIcc a x) a = deriv f a := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hs
      (hf.contDiffAt.of_le (by norm_num)) left_mem_uIcc]
    rw [iteratedDeriv_one]
  have hc : taylorWithinEval f 1 (uIcc a x) a x = f a+(x-a)*deriv f a := by
    norm_num [taylorWithinEval_succ, taylor_within_zero_eval, h1, smul_eq_mul]
    <;> ring_nf <;> simp
  have hr := heat_taylor.scalar_remainder_bound f a x B 1 hf.contDiffOn hB
  rw [hc] at hr
  convert hr using 1 <;> norm_num

/-- Bounded curvature controls a centered difference without an h^-2 loss.
This is the missing estimate needed for the differentiated-error proof of A^2 consistency. -/
theorem centered_curvature_bound (f : Real → Real) (a h B : Real)
    (hh : 0 < h) (hf : ContDiff Real 2 f)
    (hB : ∀ y, |iteratedDeriv 2 f y| ≤ B) :
    |(f (a+h)-2*f a+f (a-h))/h^2| ≤ B := by
  have hp := linear_error f a (a+h) B (by linarith) hf (fun y _ => hB y)
  have hm := linear_error f a (a-h) B (by linarith) hf (fun y _ => hB y)
  rw [show a+h-a=h by ring, abs_of_pos hh] at hp
  rw [show a-h-a= -h by ring, abs_neg, abs_of_pos hh] at hm
  have heq : f (a+h)-2*f a+f (a-h) =
      (f (a+h)-(f a+h*deriv f a)) + (f (a-h)-(f a+(-h)*deriv f a)) := by ring
  rw [heq, abs_div, abs_of_pos (sq_pos_of_pos hh)]
  apply (div_le_iff₀ (sq_pos_of_pos hh)).2
  calc
    |(f (a+h)-(f a+h*deriv f a)) + (f (a-h)-(f a+(-h)*deriv f a))| ≤
      |f (a+h)-(f a+h*deriv f a)| + |f (a-h)-(f a+(-h)*deriv f a)| := abs_add_le _ _
    _ ≤ B*h^2/2 + B*h^2/2 := add_le_add hp hm
    _ = B*h^2 := by ring
end heat_consistency_bridge
#print axioms heat_consistency_bridge.cubic_error

#print axioms heat_consistency_bridge.centered_consistency


#print axioms heat_consistency_bridge.time_quadratic_error


#print axioms heat_consistency_bridge.linear_error
#print axioms heat_consistency_bridge.centered_curvature_bound

