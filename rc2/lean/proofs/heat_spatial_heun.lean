import proofs.heat_operator_form
import proofs.heat_grid_bridge
import proofs.heat_squared_consistency

/-! Candidate connection of spatial consistency to the actual finite-grid Heun
update. These results still need compilation and are not C execution proofs. -/
namespace heat_spatial_heun
open heat_1d.FiniteGrid heat_boundary heat_grid_bridge
open heat_consistency_bridge heat_squared_consistency

/-- Sampling respects both applications of the grid operator, including endpoints. -/
theorem heun_sampling {n : Nat} (D dt h : Real) (f : Real → Real)
    (hl : Reflection 0 f) (hr : Reflection ((n : Real)*h) f) (i : Fin n) :
    heun D dt h (fun j => f (cell h j)) i =
      f (cell h i) + dt*D*centered h f (cell h i) +
      dt^2*D^2/2*centered h (centered h f) (cell h i) := by
  have ha : heatOperator D h (fun j => f (cell h j)) i =
      D*centered h f (cell h i) := by
    change D*gridCentered h (fun j => f (cell h j)) i = _
    rw [centered_sampling h f hl hr i]
  have haa : heatOperator D h (heatOperator D h (fun j => f (cell h j))) i =
      D^2*centered h (centered h f) (cell h i) := by
    calc
      _ = D^2*gridCentered h (gridCentered h (fun j : Fin n => f (cell h j))) i := by
        simp only [heatOperator, gridCentered, heat_1d.discreteSecondDeriv]
        ring
      _ = _ := by rw [centered_squared_sampling h f hl hr i]
  rw [heun_operator_polynomial, ha, haa]
  ring

/-- Spatial part of the full step defect, with both bounds derived from C6
regularity. Time derivatives and the PDE must be connected separately. -/
theorem spatial_step_error {n : Nat} (D dt h M4 M6 : Real) (f : Real → Real)
    (hh : 0 < h) (hD : 0 ≤ D) (ht : 0 ≤ dt)
    (hf : ContDiff Real 6 f)
    (hl : Reflection 0 f) (hr : Reflection ((n : Real)*h) f)
    (h4 : ∀ y, |iteratedDeriv 4 f y| ≤ M4)
    (h6 : ∀ y, |iteratedDeriv 6 f y| ≤ M6) (i : Fin n) :
    |heun D dt h (fun j => f (cell h j)) i -
      (f (cell h i) + dt*D*iteratedDeriv 2 f (cell h i) +
        dt^2*D^2/2*iteratedDeriv 4 f (cell h i))| ≤
      dt*D*h^2*M4/12 + dt^2*D^2*h^2*M6/12 := by
  have hfirst : |centered h f (cell h i) - iteratedDeriv 2 f (cell h i)| ≤ M4*h^2/12 :=
    centered_consistency f (cell h i) h M4 hh (hf.of_le (by norm_num)) h4
  have hsecond := squared_centered_consistency f (cell h i) h M6 hh hf h6
  have hdtD : 0 ≤ dt*D := mul_nonneg ht hD
  have hdtD2 : 0 ≤ dt^2*D^2/2 := by positivity
  rw [heun_sampling D dt h f hl hr i]
  have split :
      f (cell h i) + dt*D*centered h f (cell h i) +
        dt^2*D^2/2*centered h (centered h f) (cell h i) -
      (f (cell h i) + dt*D*iteratedDeriv 2 f (cell h i) +
        dt^2*D^2/2*iteratedDeriv 4 f (cell h i)) =
      (dt*D)*(centered h f (cell h i)-iteratedDeriv 2 f (cell h i)) +
      (dt^2*D^2/2)*(centered h (centered h f) (cell h i)-iteratedDeriv 4 f (cell h i)) := by ring
  rw [split]
  calc
    _ ≤ |(dt*D)*(centered h f (cell h i)-iteratedDeriv 2 f (cell h i))| +
        |(dt^2*D^2/2)*(centered h (centered h f) (cell h i)-iteratedDeriv 4 f (cell h i))| := abs_add_le _ _
    _ = (dt*D)*|centered h f (cell h i)-iteratedDeriv 2 f (cell h i)| +
        (dt^2*D^2/2)*|centered h (centered h f) (cell h i)-iteratedDeriv 4 f (cell h i)| := by
          rw [abs_mul (dt*D), abs_mul (dt^2*D^2/2), abs_of_nonneg hdtD, abs_of_nonneg hdtD2]
    _ ≤ (dt*D)*(M4*h^2/12) + (dt^2*D^2/2)*(M6*h^2/6) :=
      add_le_add (mul_le_mul_of_nonneg_left hfirst hdtD)
        (mul_le_mul_of_nonneg_left hsecond hdtD2)
    _ = _ := by ring
end heat_spatial_heun
#print axioms heat_spatial_heun.heun_sampling
#print axioms heat_spatial_heun.spatial_step_error
