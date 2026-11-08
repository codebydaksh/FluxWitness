import proofs.heat_spatial_heun

/-! Candidate one-step defect theorem. It derives the actual update's defect
from spatial/time regularity and derivative identities. The time identities
are explicit premises to be proved from the chosen PDE solution, not a claim
that an arbitrary function satisfies the heat equation. No C claim. -/
namespace heat_local_defect
open Set heat_1d.FiniteGrid heat_boundary heat_grid_bridge
open heat_spatial_heun heat_consistency_bridge

theorem heun_local_defect {n : Nat} (v : Real → Real → Real)
    (D h t dt M4 M6 : Real) (i : Fin n)
    (hh : 0 < h) (hD : 0 ≤ D) (ht : 0 ≤ dt)
    (hsmooth : ContDiff Real 6 (fun x => v x t))
    (htsmooth : ContDiff Real 3 (fun s => v (cell h i) s))
    (hl : Reflection 0 (fun x => v x t))
    (hr : Reflection ((n : Real)*h) (fun x => v x t))
    (h4 : ∀ x, |iteratedDeriv 4 (fun y => v y t) x| ≤ M4)
    (h6 : ∀ x, |iteratedDeriv 6 (fun y => v y t) x| ≤ M6)
    (hfirst : deriv (fun s => v (cell h i) s) t =
      D*iteratedDeriv 2 (fun x => v x t) (cell h i))
    (hsecond : iteratedDeriv 2 (fun s => v (cell h i) s) t =
      D^2*iteratedDeriv 4 (fun x => v x t) (cell h i))
    (hthird : ∀ s ∈ uIoo t (t+dt),
      |iteratedDeriv 3 (fun q => v (cell h i) q) s| ≤ D^3*M6) :
    |heun D dt h (fun j => v (cell h j) t) i - v (cell h i) (t+dt)| ≤
      dt*D*h^2*M4/12 + dt^2*D^2*h^2*M6/12 + dt^3*D^3*M6/6 := by
  have hs := spatial_step_error D dt h M4 M6 (fun x => v x t)
    hh hD ht hsmooth hl hr h4 h6 i
  have htaylor := time_quadratic_error (fun s => v (cell h i) s) t dt (D^3*M6)
    ht htsmooth hthird
  have hp : v (cell h i) t + dt*deriv (fun s => v (cell h i) s) t +
      dt^2/2*iteratedDeriv 2 (fun s => v (cell h i) s) t =
      v (cell h i) t + dt*D*iteratedDeriv 2 (fun x => v x t) (cell h i) +
      dt^2*D^2/2*iteratedDeriv 4 (fun x => v x t) (cell h i) := by
    rw [hfirst, hsecond]
    ring
  rw [hp] at htaylor
  let p := v (cell h i) t + dt*D*iteratedDeriv 2 (fun x => v x t) (cell h i) +
      dt^2*D^2/2*iteratedDeriv 4 (fun x => v x t) (cell h i)
  calc
    _ ≤ |heun D dt h (fun j => v (cell h j) t) i - p| +
        |p - v (cell h i) (t+dt)| := abs_sub_le _ _ _
    _ = |heun D dt h (fun j => v (cell h j) t) i - p| +
        |v (cell h i) (t+dt) - p| := by rw [abs_sub_comm p]
    _ ≤ (dt*D*h^2*M4/12 + dt^2*D^2*h^2*M6/12) + (D^3*M6)*dt^3/6 :=
      add_le_add hs htaylor
    _ = _ := by ring
end heat_local_defect
#print axioms heat_local_defect.heun_local_defect
