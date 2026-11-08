import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! Reflection identities needed to justify clamped ghost cells on a cell-centered
heat grid, including the second application of the centered operator.
These are algebraic boundary lemmas, not consistency estimates. -/
namespace heat_boundary

noncomputable def centered (h : Real) (f : Real → Real) (x : Real) : Real :=
  (f (x + h) - 2 * f x + f (x - h)) / h^2

def Reflection (a : Real) (f : Real → Real) : Prop :=
  ∀ x, f (2*a-x) = f x

theorem centered_reflection (a h : Real) (f : Real → Real)
    (hf : Reflection a f) : Reflection a (centered h f) := by
  intro x
  have hp : f (2*a-x+h) = f (x-h) := by
    calc
      f (2*a-x+h) = f (2*a-(x-h)) := by congr 1 <;> ring
      _ = f (x-h) := hf (x-h)
  have hm : f (2*a-x-h) = f (x+h) := by
    calc
      f (2*a-x-h) = f (2*a-(x+h)) := by congr 1 <;> ring
      _ = f (x+h) := hf (x+h)
  dsimp [centered]
  rw [hp, hm, hf x]
  ring

theorem reflected_half_cell (a h : Real) (f : Real → Real)
    (hf : Reflection a f) : f (a-h/2) = f (a+h/2) := by
  calc
    f (a-h/2) = f (2*a-(a+h/2)) := by congr 1 <;> ring
    _ = f (a+h/2) := hf (a+h/2)

/-- The first centered difference has the same ghost-value identity. This is
needed for A squared at the endpoints; reflection of f alone is not enough
without proving preservation by the operator. -/
theorem centered_half_cell (a h : Real) (f : Real → Real)
    (hf : Reflection a f) :
    centered h f (a-h/2) = centered h f (a+h/2) :=
  reflected_half_cell a h (centered h f) (centered_reflection a h f hf)

end heat_boundary
#print axioms heat_boundary.centered_reflection
#print axioms heat_boundary.reflected_half_cell
#print axioms heat_boundary.centered_half_cell
