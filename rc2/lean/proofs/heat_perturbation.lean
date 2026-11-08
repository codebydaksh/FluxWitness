import proofs.heat_1d

/-! Conditional propagation of implementation perturbations through the actual
Heun scheme. Candidate awaiting compilation. The per-step implementation bound
is an explicit unproved premise here, not a floating-point correctness claim. -/
namespace heat_1d.FiniteGrid

 theorem perturbed_error_budget {n : Nat} (D dx initial : Real)
    (dt defect perturbation : Nat → Real)
    (computed reference : Nat → Fin n → Real)
    (hdx : 0 < dx) (hD : 0 ≤ D)
    (hdt : ∀ k, 0 ≤ dt k) (hCFL : ∀ k, 2*D*dt k ≤ dx*dx)
    (hinit : Bounded (-initial) initial (fun i => computed 0 i-reference 0 i))
    (hdefect : ∀ k, Bounded (-(defect k)) (defect k)
      (fun i => heun D (dt k) dx (reference k) i-reference (k+1) i))
    (hperturb : ∀ k, Bounded (-(perturbation k)) (perturbation k)
      (fun i => computed (k+1) i-heun D (dt k) dx (computed k) i))
    (k : Nat) :
    Bounded (-(errorBudget initial (fun j => defect j+perturbation j) k))
      (errorBudget initial (fun j => defect j+perturbation j) k)
      (fun i => computed k i-reference k i) := by
  induction k with
  | zero => exact hinit
  | succ k ih =>
    have hstep := heun_difference_bounded D (dt k) dx
      (errorBudget initial (fun j => defect j+perturbation j) k)
      (computed k) (reference k) hdx hD (hdt k) (hCFL k) ih
    intro i
    obtain ⟨hlo,hhi⟩ := hstep i
    obtain ⟨dlo,dhi⟩ := hdefect k i
    obtain ⟨plo,phi⟩ := hperturb k i
    simp only [errorBudget]
    constructor <;> linarith

end heat_1d.FiniteGrid
#print axioms heat_1d.FiniteGrid.perturbed_error_budget
