import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Algebraic assembly of two proved Taylor bounds into centered-stencil consistency.
The Taylor bounds remain explicit premises; this module alone is not a PDE consistency proof. -/
namespace heat_stencil_error

theorem centered_from_cubic_remainders
    (uL u0 uR d1 d2 d3 h M : Real) (hh : 0 < h)
    (hp : |uR - (u0 + h*d1 + h^2/2*d2 + h^3/6*d3)| ≤ M*h^4/24)
    (hm : |uL - (u0 - h*d1 + h^2/2*d2 - h^3/6*d3)| ≤ M*h^4/24) :
    |(uR - 2*u0 + uL)/h^2 - d2| ≤ M*h^2/12 := by
  have hh2 : 0 < h^2 := sq_pos_of_pos hh
  have heq : (uR - 2*u0 + uL)/h^2 - d2 =
      ((uR - (u0 + h*d1 + h^2/2*d2 + h^3/6*d3)) +
       (uL - (u0 - h*d1 + h^2/2*d2 - h^3/6*d3)))/h^2 := by
    field_simp [ne_of_gt hh]
    <;> ring
  rw [heq, abs_div, abs_of_pos hh2]
  apply (div_le_iff₀ hh2).2
  calc
    |(uR - (u0 + h*d1 + h^2/2*d2 + h^3/6*d3)) +
       (uL - (u0 - h*d1 + h^2/2*d2 - h^3/6*d3))| ≤
      |uR - (u0 + h*d1 + h^2/2*d2 + h^3/6*d3)| +
      |uL - (u0 - h*d1 + h^2/2*d2 - h^3/6*d3)| := abs_add_le _ _
    _ ≤ M*h^4/24 + M*h^4/24 := add_le_add hp hm
    _ = M*h^2/12 * h^2 := by ring

end heat_stencil_error
#print axioms heat_stencil_error.centered_from_cubic_remainders

