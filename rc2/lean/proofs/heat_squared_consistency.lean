import proofs.heat_consistency_bridge
import proofs.heat_centered_derivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Candidate squared-stencil consistency from C6 regularity. This file is not
certified or installed until its full source and declaration audit succeeds. -/
namespace heat_squared_consistency
open heat_boundary heat_centered_derivatives heat_consistency_bridge

private theorem iterated_two (f : Real → Real) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show 2 = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

private theorem iterated_four_of_two (f : Real → Real) :
    iteratedDeriv 4 (deriv (deriv f)) = iteratedDeriv 6 f := by
  symm
  calc
    iteratedDeriv 6 f = iteratedDeriv 5 (deriv f) := iteratedDeriv_succ'
    _ = iteratedDeriv 4 (deriv (deriv f)) := iteratedDeriv_succ'

private theorem iterated_two_of_two (f : Real → Real) :
    iteratedDeriv 2 (deriv (deriv f)) = iteratedDeriv 4 f := by
  symm
  calc
    iteratedDeriv 4 f = iteratedDeriv 3 (deriv f) := iteratedDeriv_succ'
    _ = iteratedDeriv 2 (deriv (deriv f)) := iteratedDeriv_succ'

/-- The second application of the centered stencil approximates f'''' with
error at most h^2 M6/6. Unlike a bound obtained by dividing first-stencil errors
by h^2, this estimate retains second-order spatial consistency. -/
theorem squared_centered_consistency (f : Real → Real) (x h M : Real)
    (hh : 0 < h) (hf : ContDiff Real 6 f)
    (hM : ∀ y, |iteratedDeriv 6 f y| ≤ M) :
    |centered h (centered h f) x - iteratedDeriv 4 f x| ≤ M*h^2/6 := by
  have hf5 : ContDiff Real 5 (deriv f) := hf.deriv'
  have hf4 : ContDiff Real 4 (deriv (deriv f)) := hf5.deriv'
  have hd : Differentiable Real f := hf.differentiable (by norm_num)
  have hd' : Differentiable Real (deriv f) := hf5.differentiable (by norm_num)
  have hc2 : ContDiff Real 2 (centered h f) :=
    contDiff_centered 2 h f (hf.of_le (by norm_num))
  have hf2 : ContDiff Real 2 (deriv (deriv f)) := hf4.of_le (by norm_num)
  let e : Real → Real := fun y => centered h f y - deriv (deriv f) y
  have he2 : ContDiff Real 2 e := hc2.sub hf2
  have herr (y : Real) :
      |centered h (deriv (deriv f)) y - iteratedDeriv 4 f y| ≤ M*h^2/12 := by
    have H := centered_consistency (deriv (deriv f)) y h M hh hf4
      (fun z => by simpa only [iterated_four_of_two] using hM z)
    simpa only [centered, iterated_two_of_two] using H
  have heder (y : Real) : iteratedDeriv 2 e y =
      centered h (deriv (deriv f)) y - iteratedDeriv 4 f y := by
    change iteratedDeriv 2 (fun z => centered h f z - deriv (deriv f) z) y = _
    rw [iteratedDeriv_fun_sub hc2.contDiffAt hf2.contDiffAt,
      iterated_two (centered h f), second_deriv_centered h f hd hd',
      iterated_two_of_two]
  have heB : ∀ y, |iteratedDeriv 2 e y| ≤ M*h^2/12 := by
    intro y
    rw [heder]
    exact herr y
  have heC : |centered h e x| ≤ M*h^2/12 :=
    centered_curvature_bound e x h (M*h^2/12) hh he2 heB
  have split : centered h (centered h f) x - iteratedDeriv 4 f x =
      centered h e x +
      (centered h (deriv (deriv f)) x - iteratedDeriv 4 f x) := by
    dsimp [centered, e]
    ring
  rw [split]
  calc
    _ ≤ |centered h e x| +
        |centered h (deriv (deriv f)) x - iteratedDeriv 4 f x| := abs_add_le _ _
    _ ≤ M*h^2/12 + M*h^2/12 := add_le_add heC (herr x)
    _ = M*h^2/6 := by ring
end heat_squared_consistency
#print axioms heat_squared_consistency.squared_centered_consistency
