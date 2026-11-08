import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

import Mathlib.Tactic.Convert

import Mathlib.Tactic.Ring

/-! A nonconstant exact heat-equation reference with compatible Neumann boundaries.

This supplies the analytic reference for the convergence target; it does not

by itself prove numerical convergence, derivative bounds, or C correctness. -/

namespace heat_reference

noncomputable def profile (D k x t : Real) : Real :=

  Real.exp (-D * k^2 * t) * Real.cos (k * x)

noncomputable def spatialDerivative (D k x t : Real) : Real :=

  -Real.exp (-D * k^2 * t) * k * Real.sin (k * x)

theorem time_derivative (D k x t : Real) :

    HasDerivAt (fun s => profile D k x s) (-D * k^2 * profile D k x t) t := by

  have h := ((Real.hasDerivAt_exp (-D * k^2 * t)).comp t

    ((hasDerivAt_id t).const_mul (-D * k^2))).mul_const (Real.cos (k * x))

  convert! h using 1 <;> (try funext y) <;> (try dsimp [profile, Function.comp_def]) <;> ring

theorem space_derivative (D k x t : Real) :

    HasDerivAt (fun y => profile D k y t) (spatialDerivative D k x t) x := by

  have h := ((Real.hasDerivAt_cos (k * x)).comp x

    ((hasDerivAt_id x).const_mul k)).const_mul (Real.exp (-D * k^2 * t))

  convert! h using 1 <;> (try funext y) <;> (try dsimp [profile, spatialDerivative, Function.comp_def]) <;> ring

theorem space_second_derivative (D k x t : Real) :

    HasDerivAt (fun y => spatialDerivative D k y t) (-k^2 * profile D k x t) x := by

  have h := ((Real.hasDerivAt_sin (k * x)).comp x

    ((hasDerivAt_id x).const_mul k)).const_mul (-Real.exp (-D * k^2 * t) * k)

  convert! h using 1 <;> (try funext y) <;> (try dsimp [profile, spatialDerivative, Function.comp_def]) <;> ring

/-- The actual partial-derivative equation, derived from the differentiation lemmas. -/

theorem solves_heat_equation (D k x t : Real) :

    deriv (fun s => profile D k x s) t =

      D * deriv (fun y => deriv (fun z => profile D k z t) y) x := by

  have hx : (fun y => deriv (fun z => profile D k z t) y) =

      (fun y => spatialDerivative D k y t) := by

    funext y

    exact (space_derivative D k y t).deriv

  rw [(time_derivative D k x t).deriv, hx, (space_second_derivative D k x t).deriv]

  ring

theorem initial_value (D k x : Real) : profile D k x 0 = Real.cos (k * x) := by

  simp [profile]

theorem neumann_left (D k t : Real) : deriv (fun x => profile D k x t) 0 = 0 := by

  rw [(space_derivative D k 0 t).deriv]

  simp [spatialDerivative]

theorem neumann_right (D L t : Real) (hL : L ≠ 0) :

    deriv (fun x => profile D (Real.pi / L) x t) L = 0 := by

  rw [(space_derivative D (Real.pi / L) L t).deriv]

  simp [spatialDerivative, div_mul_cancel₀ _ hL]

theorem even_extension (D k x t : Real) : profile D k (-x) t = profile D k x t := by

  simp [profile]

end heat_reference

#print axioms heat_reference.time_derivative

#print axioms heat_reference.space_derivative

#print axioms heat_reference.space_second_derivative

#print axioms heat_reference.solves_heat_equation

#print axioms heat_reference.initial_value

#print axioms heat_reference.neumann_left

#print axioms heat_reference.neumann_right

#print axioms heat_reference.even_extension

