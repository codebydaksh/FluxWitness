import proofs.heat_1d

/-! Candidate affine preservation for the actual clamped-grid update. This is
needed to transfer the unit-cosine reference to the offset/scaled benchmark.
It concerns exact reals only and does not assert bitwise floating preservation. -/
namespace heat_1d.FiniteGrid

theorem heun_affine {n : Nat} (D dt h a b : Real) (u : Fin n → Real) :
    heun D dt h (fun i => a*u i+b) =
      fun i => a*heun D dt h u i+b := by
  funext i
  simp only [heun, euler, heat_1d.discreteSecondDeriv]
  ring

theorem evolve_affine {n : Nat} (D h a b : Real) (dt : Nat → Real)
    (u0 : Fin n → Real) (K : Nat) :
    evolve D h dt (fun i => a*u0 i+b) K =
      fun i => a*evolve D h dt u0 K i+b := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [evolve, ih]
    exact heun_affine D (dt K) h a b (evolve D h dt u0 K)

/-- Transfers an already proved pointwise error bound through an affine map.
Note the spaces around `*`: `|a|*e` lexes the closing bar and `*` as one token. -/
theorem affine_error_bound (a b u v e : Real) (huv : |u-v| ≤ e) :
    |(a*u+b)-(a*v+b)| ≤ |a| * e := by
  rw [show (a*u+b)-(a*v+b) = a*(u-v) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_left huv (abs_nonneg a)

end heat_1d.FiniteGrid
#print axioms heat_1d.FiniteGrid.heun_affine
#print axioms heat_1d.FiniteGrid.evolve_affine
#print axioms heat_1d.FiniteGrid.affine_error_bound
