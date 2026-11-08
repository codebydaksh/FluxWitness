import proofs.heat_convergence
import proofs.heat_reference_bounds
import Mathlib.Tactic.FunProp

/-! Candidate nonconstant cosine instantiation of the analytic convergence
conditions. Compile and audit before claiming a proved benchmark. -/
namespace heat_cosine_conditions
open Set heat_1d.FiniteGrid heat_reference heat_convergence

private theorem elapsed_nonnegative (dt : Nat → Real) (ht : ∀ j, 0 ≤ dt j) :
    ∀ j, 0 ≤ elapsed dt j := by
  intro j
  induction j with
  | zero => simp [elapsed]
  | succ j ih => exact add_nonneg ih (ht j)

/-- The frequency condition is kL=pi with L=n*h. It enforces both reflecting
boundaries. Taking k=pi/L requires L nonzero, to be discharged by the caller. -/
theorem cosine_conditions (n : Nat) (D h k : Real) (dt : Nat → Real)
    (hD : 0 ≤ D) (ht : ∀ j, 0 ≤ dt j) (hk : k*((n : Real)*h) = Real.pi) :
    ReferenceConditions n D h (k^4) (k^6) dt (fun x t => profile D k x t) := by
  constructor
  · intro j
    unfold profile
    fun_prop
  · intro x
    unfold profile
    fun_prop
  · intro j x
    simpa only [mul_zero, zero_sub] using even_extension D k x (elapsed dt j)
  · intro j x
    dsimp [profile]
    have angle : k*(2*((n : Real)*h)-x) = 2*Real.pi-k*x := by
      calc
        _ = 2*(k*((n : Real)*h))-k*x := by ring
        _ = _ := by rw [hk]
    rw [angle, Real.cos_two_pi_sub]
  · intro j x
    exact fourth_spatial_bound D k x (elapsed dt j) hD (elapsed_nonnegative dt ht j)
  · intro j x
    exact sixth_spatial_bound D k x (elapsed dt j) hD (elapsed_nonnegative dt ht j)
  · intro j x
    rw [(time_derivative D k x (elapsed dt j)).deriv]
    have hs := congrFun (space_iterated_even D k (elapsed dt j) 1) x
    change iteratedDeriv 2 (fun y => profile D k y (elapsed dt j)) x = _ at hs
    rw [hs]
    ring
  · intro j x
    rw [time_iterated]
    have hs := congrFun (space_iterated_even D k (elapsed dt j) 2) x
    change iteratedDeriv 4 (fun y => profile D k y (elapsed dt j)) x = _ at hs
    rw [hs]
    ring
  · intro j x s hs
    rw [uIoo_of_le (le_add_of_nonneg_right (ht j))] at hs
    have hs0 : 0 ≤ s := le_trans (elapsed_nonnegative dt ht j) hs.1.le
    exact third_time_bound D k x s hD hs0

/-- Concrete cosine convergence target for the original exact-real clamped
scheme, with no unproved local-defect premise. This candidate still needs Lean
acceptance and a separate C/float correspondence proof. -/
theorem cosine_error_bound {n : Nat} (D h k initial cap T : Real)
    (dt : Nat → Real) (u0 : Fin n → Real)
    (hh : 0 < h) (hD : 0 ≤ D) (hk : k*((n : Real)*h) = Real.pi)
    (hcap0 : 0 ≤ cap) (ht : ∀ j, 0 ≤ dt j) (hcap : ∀ j, dt j ≤ cap)
    (hCFL : ∀ j, 2*D*dt j ≤ h*h)
    (hinit : Bounded (-initial) initial
      (fun i => u0 i-Real.cos (k*heat_grid_bridge.cell h i)))
    (K : Nat) (hT : elapsed dt K ≤ T) (i : Fin n) :
    |evolve D h dt u0 K i - profile D k (heat_grid_bridge.cell h i) (elapsed dt K)| ≤
      initial + (D*h^2*k^4/12 + (D^2*h^2*k^6/12)*cap + (D^3*k^6/6)*cap^2)*T := by
  have hstart : Bounded (-initial) initial
      (fun j => u0 j-profile D k (heat_grid_bridge.cell h j) 0) := by
    simpa only [initial_value] using hinit
  exact exact_error_bound D h (k^4) (k^6) initial cap T dt
    (fun x t => profile D k x t) u0 hh hD (by positivity) (by positivity)
    hcap0 ht hcap hCFL (cosine_conditions n D h k dt hD ht hk) hstart K hT i

end heat_cosine_conditions
#print axioms heat_cosine_conditions.cosine_conditions

#print axioms heat_cosine_conditions.cosine_error_bound
