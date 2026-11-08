import proofs.heat_1d
import proofs.heat_boundary
import Mathlib.Tactic.NormNum

/-! Sampling bridge for the actual clamped, cell-centred heat grid.
Candidate, not yet certified. No floating-point claim. -/
namespace heat_grid_bridge
open heat_1d.FiniteGrid heat_boundary

noncomputable def cell {n : Nat} (h : Real) (i : Fin n) : Real :=
  ((i.val : Real) + 1/2) * h

 theorem sample_left {n : Nat} (h : Real) (f : Real → Real)
    (hf : Reflection 0 f) (i : Fin n) :
    f (cell h (left i)) = f (cell h i - h) := by
  by_cases hz : i.val = 0
  · have hc : cell h i = h/2 := by simp [cell, hz]; ring
    have hl : cell h (left i) = h/2 := by simp [cell, left, hz]; ring
    rw [hc, hl]
    have he := reflected_half_cell 0 h f hf
    convert he.symm using 1 <;> congr 1 <;> ring
  · congr 1
    have hp : 1 ≤ i.val := by omega
    simp only [cell, left]
    rw [Nat.cast_sub hp]
    push_cast
    ring

 theorem sample_right {n : Nat} (h : Real) (f : Real → Real)
    (hf : Reflection ((n : Real)*h) f) (i : Fin n) :
    f (cell h (right i)) = f (cell h i + h) := by
  by_cases hr : i.val + 1 < n
  · congr 1
    simp [cell, right, hr]
    <;> ring
  · have hn : i.val + 1 = n := by omega
    have hnR : (i.val : Real) + 1 = (n : Real) := by exact_mod_cast hn
    have hc : cell h i = (n : Real)*h-h/2 := by dsimp [cell]; rw [← hnR]; ring
    simp only [right, dif_neg hr]
    rw [hc]
    have he := reflected_half_cell ((n : Real)*h) h f hf
    convert he using 1 <;> congr 1 <;> ring

noncomputable def gridCentered {n : Nat} (h : Real) (u : Fin n → Real) : Fin n → Real :=
  fun i => heat_1d.discreteSecondDeriv (u (left i)) (u i) (u (right i)) h

 theorem centered_sampling {n : Nat} (h : Real) (f : Real → Real)
    (hl : Reflection 0 f) (hr : Reflection ((n : Real)*h) f) (i : Fin n) :
    gridCentered h (fun j => f (cell h j)) i = centered h f (cell h i) := by
  dsimp [gridCentered]
  rw [sample_left h f hl i, sample_right h f hr i]
  simp only [heat_1d.discreteSecondDeriv, centered, pow_two]

 theorem centered_squared_sampling {n : Nat} (h : Real) (f : Real → Real)
    (hl : Reflection 0 f) (hr : Reflection ((n : Real)*h) f) (i : Fin n) :
    gridCentered h (gridCentered h (fun j => f (cell h j))) i =
      centered h (centered h f) (cell h i) := by
  have hfun : gridCentered h (fun j : Fin n => f (cell h j)) =
      (fun j : Fin n => centered h f (cell h j)) := by
    funext j
    exact centered_sampling h f hl hr j
  rw [hfun]
  exact centered_sampling h (centered h f)
    (centered_reflection 0 h f hl) (centered_reflection ((n : Real)*h) h f hr) i

end heat_grid_bridge
#print axioms heat_grid_bridge.sample_left
#print axioms heat_grid_bridge.sample_right
#print axioms heat_grid_bridge.centered_sampling
#print axioms heat_grid_bridge.centered_squared_sampling
