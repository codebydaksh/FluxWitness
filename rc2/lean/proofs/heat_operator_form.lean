import proofs.heat_1d

/-! Exact operator form of the complete implemented Heun update.
Candidate awaiting compilation and axiom audit. No PDE or floating-point claim. -/
namespace heat_1d.FiniteGrid

noncomputable def heatOperator {n : Nat} (D dx : Real) (u : Fin n → Real) : Fin n → Real :=
  fun i => D * discreteSecondDeriv (u (left i)) (u i) (u (right i)) dx

/-- Identifies the actual two-stage update with I + dt A + dt^2 A^2/2.
This identity is needed to apply both spatial consistency estimates to Heun. -/
theorem heun_operator_polynomial {n : Nat} (D dt dx : Real) (u : Fin n → Real)
    (i : Fin n) :
    heun D dt dx u i = u i + dt * heatOperator D dx u i +
      dt^2 / 2 * heatOperator D dx (heatOperator D dx u) i := by
  simp only [heun, euler, heatOperator, discreteSecondDeriv]
  ring

end heat_1d.FiniteGrid
#print axioms heat_1d.FiniteGrid.heun_operator_polynomial
