import Mathlib.Analysis.Calculus.ContDiff.Operations
import proofs.heat_boundary
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Derivative commutation for the actual centered stencil. Candidate only;
compile and audit before use. Differentiability premises are explicit. -/
namespace heat_centered_derivatives
open heat_boundary

 theorem hasDerivAt_centered (h : Real) (f : Real → Real) (x : Real)
    (hf : Differentiable Real f) :
    HasDerivAt (centered h f) (centered h (deriv f) x) x := by
  have hp := (hf (x+h)).hasDerivAt.comp x ((hasDerivAt_id x).add_const h)
  have hm := (hf (x-h)).hasDerivAt.comp x ((hasDerivAt_id x).sub_const h)
  have hc := ((hp.sub ((hf x).hasDerivAt.const_mul 2)).add hm).div_const (h^2)
  convert! hc using 1 <;> simp [centered, Function.comp_def]

 theorem differentiable_centered (h : Real) (f : Real → Real)
    (hf : Differentiable Real f) : Differentiable Real (centered h f) :=
  fun x => (hasDerivAt_centered h f x hf).differentiableAt

 theorem deriv_centered (h : Real) (f : Real → Real)
    (hf : Differentiable Real f) :
    deriv (centered h f) = centered h (deriv f) := by
  funext x
  exact (hasDerivAt_centered h f x hf).deriv

 theorem second_deriv_centered (h : Real) (f : Real → Real)
    (hf : Differentiable Real f) (hf' : Differentiable Real (deriv f)) :
    deriv (deriv (centered h f)) = centered h (deriv (deriv f)) := by
  rw [deriv_centered h f hf, deriv_centered h (deriv f) hf']

/-- The centered operator preserves the smoothness needed for the error argument. -/
theorem contDiff_centered (n : Nat) (h : Real) (f : Real → Real)
    (hf : ContDiff Real n f) : ContDiff Real n (centered h f) := by
  have hp : ContDiff Real n (fun x : Real => f (x+h)) :=
    hf.comp (contDiff_id.add contDiff_const)
  have hm : ContDiff Real n (fun x : Real => f (x-h)) :=
    hf.comp (contDiff_id.sub contDiff_const)
  have hc : ContDiff Real n (fun x : Real => 2*f x) := contDiff_const.mul hf
  convert! ((hp.sub hc).add hm).div_const (h^2) using 1 <;> simp [centered]
end heat_centered_derivatives
#print axioms heat_centered_derivatives.hasDerivAt_centered
#print axioms heat_centered_derivatives.differentiable_centered
#print axioms heat_centered_derivatives.deriv_centered
#print axioms heat_centered_derivatives.second_deriv_centered

#print axioms heat_centered_derivatives.contDiff_centered

