import proofs.heat_1d

/-! Algebra for the final error-budget summation. Candidate, not certified.
This does not assume or establish a PDE defect estimate; it converts an explicit
polynomial step budget into its elapsed-time bound. -/
namespace heat_1d.FiniteGrid

noncomputable def elapsed (dt : Nat → Real) : Nat → Real
  | 0 => 0
  | k+1 => elapsed dt k + dt k

 theorem polynomial_step_bound (a b c dt cap : Real)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (ht : 0 ≤ dt) (hcap : dt ≤ cap) :
    a*dt + b*dt^2 + c*dt^3 ≤ (a+b*cap+c*cap^2)*dt := by
  have hp : 0 ≤ cap := le_trans ht hcap
  have h2 : dt^2 ≤ cap*dt := by nlinarith
  have hs : dt^2 ≤ cap^2 := by nlinarith
  have h3 : dt^3 ≤ cap^2*dt := by
    nlinarith [mul_le_mul_of_nonneg_right hs ht]
  calc
    a*dt + b*dt^2 + c*dt^3 ≤ a*dt + b*(cap*dt) + c*(cap^2*dt) :=
      add_le_add (add_le_add (le_refl (a*dt)) (mul_le_mul_of_nonneg_left h2 hb))
        (mul_le_mul_of_nonneg_left h3 hc)
    _ = (a+b*cap+c*cap^2)*dt := by ring

 theorem polynomial_budget_bound (initial a b c cap : Real) (dt : Nat → Real)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (ht : ∀ k, 0 ≤ dt k) (hcap : ∀ k, dt k ≤ cap)
    (k : Nat) :
    errorBudget initial (fun j => a*dt j+b*(dt j)^2+c*(dt j)^3) k ≤
      initial + (a+b*cap+c*cap^2)*elapsed dt k := by
  induction k with
  | zero => simp [errorBudget, elapsed]
  | succ k ih =>
    have hstep := polynomial_step_bound a b c (dt k) cap hb hc (ht k) (hcap k)
    simp only [errorBudget, elapsed]
    nlinarith

 theorem polynomial_budget_final_time (initial a b c cap T : Real) (dt : Nat → Real)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcap0 : 0 ≤ cap)
    (ht : ∀ k, 0 ≤ dt k) (hcap : ∀ k, dt k ≤ cap)
    (k : Nat) (hT : elapsed dt k ≤ T) :
    errorBudget initial (fun j => a*dt j+b*(dt j)^2+c*(dt j)^3) k ≤
      initial + (a+b*cap+c*cap^2)*T := by
  have hbudget := polynomial_budget_bound initial a b c cap dt hb hc ht hcap k
  have hC : 0 ≤ a+b*cap+c*cap^2 := by positivity
  exact le_trans hbudget (add_le_add (le_refl initial) (mul_le_mul_of_nonneg_left hT hC))

end heat_1d.FiniteGrid
#print axioms heat_1d.FiniteGrid.polynomial_step_bound
#print axioms heat_1d.FiniteGrid.polynomial_budget_bound
#print axioms heat_1d.FiniteGrid.polynomial_budget_final_time

