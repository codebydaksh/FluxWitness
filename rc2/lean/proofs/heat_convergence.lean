import proofs.heat_local_defect
import proofs.heat_error_accumulation

/-! Candidate exact-real convergence assembly. The reference conditions expose
all analytic obligations. A cosine instantiation must discharge them; neither
this record nor the theorem supplies C or floating-point correctness. -/
namespace heat_convergence
open Set heat_1d.FiniteGrid heat_boundary heat_grid_bridge heat_local_defect

structure ReferenceConditions (n : Nat) (D h M4 M6 : Real)
    (dt : Nat → Real) (v : Real → Real → Real) : Prop where
  space_smooth : ∀ k, ContDiff Real 6 (fun x => v x (elapsed dt k))
  time_smooth : ∀ x, ContDiff Real 3 (fun t => v x t)
  left_reflection : ∀ k, Reflection 0 (fun x => v x (elapsed dt k))
  right_reflection : ∀ k, Reflection ((n : Real)*h) (fun x => v x (elapsed dt k))
  fourth_bound : ∀ k x, |iteratedDeriv 4 (fun y => v y (elapsed dt k)) x| ≤ M4
  sixth_bound : ∀ k x, |iteratedDeriv 6 (fun y => v y (elapsed dt k)) x| ≤ M6
  first_time : ∀ k x, deriv (fun t => v x t) (elapsed dt k) =
    D*iteratedDeriv 2 (fun y => v y (elapsed dt k)) x
  second_time : ∀ k x, iteratedDeriv 2 (fun t => v x t) (elapsed dt k) =
    D^2*iteratedDeriv 4 (fun y => v y (elapsed dt k)) x
  third_time_bound : ∀ k x s, s ∈ uIoo (elapsed dt k) (elapsed dt k+dt k) →
    |iteratedDeriv 3 (fun t => v x t) s| ≤ D^3*M6

/-- Global error for the actual clamped-grid scheme. The one-step defect premise
of stability is discharged by the analytic local theorem, not assumed here. -/
theorem exact_error_bound {n : Nat} (D h M4 M6 initial cap T : Real)
    (dt : Nat → Real) (v : Real → Real → Real) (u0 : Fin n → Real)
    (hh : 0 < h) (hD : 0 ≤ D) (h4 : 0 ≤ M4) (h6 : 0 ≤ M6)
    (hcap0 : 0 ≤ cap) (ht : ∀ k, 0 ≤ dt k) (hcap : ∀ k, dt k ≤ cap)
    (hCFL : ∀ k, 2*D*dt k ≤ h*h)
    (hv : ReferenceConditions n D h M4 M6 dt v)
    (hinit : Bounded (-initial) initial (fun i => u0 i-v (cell h i) 0))
    (K : Nat) (hT : elapsed dt K ≤ T) (i : Fin n) :
    |evolve D h dt u0 K i - v (cell h i) (elapsed dt K)| ≤
      initial + (D*h^2*M4/12 + (D^2*h^2*M6/12)*cap + (D^3*M6/6)*cap^2)*T := by
  let a := D*h^2*M4/12
  let b := D^2*h^2*M6/12
  let c := D^3*M6/6
  let defect : Nat → Real := fun k => a*dt k+b*(dt k)^2+c*(dt k)^3
  let reference : Nat → Fin n → Real := fun k j => v (cell h j) (elapsed dt k)
  have hdefect : ∀ k, Bounded (-(defect k)) (defect k)
      (fun j => heun D (dt k) h (reference k) j-reference (k+1) j) := by
    intro k j
    apply abs_le.mp
    have H := heun_local_defect v D h (elapsed dt k) (dt k) M4 M6 j
      hh hD (ht k) (hv.space_smooth k) (hv.time_smooth (cell h j))
      (hv.left_reflection k) (hv.right_reflection k)
      (hv.fourth_bound k) (hv.sixth_bound k)
      (hv.first_time k (cell h j)) (hv.second_time k (cell h j))
      (hv.third_time_bound k (cell h j))
    change |heun D (dt k) h (fun j => v (cell h j) (elapsed dt k)) j -
      v (cell h j) (elapsed dt k+dt k)| ≤ defect k
    convert H using 1 <;> dsimp [defect,a,b,c] <;> ring
  have hstart : Bounded (-initial) initial (fun j => u0 j-reference 0 j) := by
    simpa only [reference, elapsed] using hinit
  have H := evolve_error_budget D h initial dt defect u0 reference hh hD ht hCFL hstart hdefect K i
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hsum := polynomial_budget_final_time initial a b c cap T dt
    ha hb hc hcap0 ht hcap K hT
  have Habs := abs_le.mpr H
  exact le_trans Habs hsum
end heat_convergence
#print axioms heat_convergence.exact_error_bound
