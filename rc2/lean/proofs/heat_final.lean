import proofs.heat_cosine_conditions
import proofs.heat_perturbation
import proofs.heat_affine

/-! Glue for the benchmark  a * cos(k*y) + b  (harness: a = 1/2, b = 1, y = x + 3).

Combines, as black boxes:
  * heat_cosine_conditions.cosine_error_bound   exact scheme vs unit cosine
  * heat_affine.evolve_affine / affine_error_bound   affine lift
  * heat_perturbation.perturbed_error_budget    per-step implementation perturbation

CANDIDATE, NOT COMPILED (no Lean/Mathlib where this was written). Expect small tactic repairs.
Exact reals only. `computed k i` is the C array after k steps, read as reals.

NOT discharged here:
  * `hperturb` is the per-step implementation premise (Gappa/CBMC side). It is stated for ALL steps,
    but the Gappa bound is only valid while |computed j| <= 2, which is itself a consequence of the
    error bound: circular. Needs a prefix version (premises only for j < K) plus a range induction.
  * The PDE statement for the shifted/affine reference (only `profile` itself is shown to solve the
    heat equation in heat_reference).
-/
namespace heat_final
open heat_1d.FiniteGrid heat_grid_bridge heat_reference heat_cosine_conditions

theorem budget_const (δ : Real) (K : Nat) :
    errorBudget 0 (fun _ => (0:Real) + δ) K = (K : Real) * δ := by
  induction K with
  | zero => simp [errorBudget]
  | succ K ih =>
    simp only [errorBudget, ih]
    push_cast
    ring

/-- Implementation perturbation alone: computed vs the exact-real scheme started from `computed 0`. -/
theorem perturbation_only {n : Nat} (D h δ : Real) (dt : Nat → Real)
    (computed : Nat → Fin n → Real)
    (hh : 0 < h) (hD : 0 ≤ D) (ht : ∀ k, 0 ≤ dt k) (hCFL : ∀ k, 2*D*dt k ≤ h*h)
    (hperturb : ∀ k, Bounded (-δ) δ
      (fun i => computed (k+1) i - heun D (dt k) h (computed k) i))
    (K : Nat) (i : Fin n) :
    |computed K i - evolve D h dt (computed 0) K i| ≤ (K : Real) * δ := by
  have H := perturbed_error_budget D h 0 dt (fun _ => 0) (fun _ => δ) computed
    (fun k => evolve D h dt (computed 0) k) hh hD ht hCFL
    (by intro j; simp [evolve])
    (by intro k j; simp [evolve])
    hperturb K
  calc |computed K i - evolve D h dt (computed 0) K i|
      ≤ errorBudget 0 (fun _ => (0:Real) + δ) K := abs_le.mpr (H i)
    _ = (K : Real) * δ := budget_const δ K

/-- Benchmark bound: implementation vs  a * (exp(-D k^2 t) cos(k y)) + b  at cell centres y = cell h i. -/
theorem harness_error_bound {n : Nat} (D h k a b eps0 cap T δ : Real) (dt : Nat → Real)
    (computed : Nat → Fin n → Real)
    (hh : 0 < h) (hD : 0 ≤ D) (hk : k*((n : Real)*h) = Real.pi) (ha : a ≠ 0)
    (hcap0 : 0 ≤ cap) (ht : ∀ j, 0 ≤ dt j) (hcap : ∀ j, dt j ≤ cap)
    (hCFL : ∀ j, 2*D*dt j ≤ h*h)
    (hinit : ∀ i, |computed 0 i - (a*Real.cos (k*cell h i)+b)| ≤ eps0)
    (hperturb : ∀ j, Bounded (-δ) δ
      (fun i => computed (j+1) i - heun D (dt j) h (computed j) i))
    (K : Nat) (hT : elapsed dt K ≤ T) (i : Fin n) :
    |computed K i - (a*profile D k (cell h i) (elapsed dt K)+b)| ≤
      eps0 + |a| * ((D*h^2*k^4/12 + (D^2*h^2*k^6/12)*cap + (D^3*k^6/6)*cap^2)*T)
        + (K : Real)*δ := by
  have hpert := perturbation_only D h δ dt computed hh hD ht hCFL hperturb K i
  obtain ⟨w0, hw0⟩ : ∃ w0 : Fin n → Real, w0 = fun j => (computed 0 j - b)/a := ⟨_, rfl⟩
  have hw : ∀ j, w0 j = (computed 0 j - b)/a := by
    intro j
    rw [hw0]
  have habs : |a| ≠ 0 := abs_ne_zero.mpr ha
  -- computed 0 is the affine image of the unit-cosine data w0
  have hcomp0 : computed 0 = fun j => a*w0 j + b := by
    funext j
    show computed 0 j = a * w0 j + b
    rw [hw j]
    have h1 : a * ((computed 0 j - b)/a) = computed 0 j - b := by
      first | (field_simp; ring) | field_simp
    linarith
  -- w0 is within eps0 / |a| of the unit cosine
  have hw_init : Bounded (-(eps0 / |a|)) (eps0 / |a|)
      (fun j => w0 j - Real.cos (k*cell h j)) := by
    intro j
    have e : w0 j - Real.cos (k*cell h j) =
        (computed 0 j - (a*Real.cos (k*cell h j)+b))/a := by
      rw [hw j]
      first | (field_simp; ring) | field_simp
    have hb : |w0 j - Real.cos (k*cell h j)| ≤ eps0 / |a| := by
      rw [e, abs_div]
      exact div_le_div_of_nonneg_right (hinit j) (abs_nonneg a)
    exact abs_le.mp hb
  have hcos := cosine_error_bound D h k (eps0 / |a|) cap T dt w0 hh hD hk hcap0 ht hcap hCFL
    hw_init K hT i
  have hev : evolve D h dt (computed 0) K i = a*evolve D h dt w0 K i + b := by
    rw [hcomp0, evolve_affine]
  have hexact : |evolve D h dt (computed 0) K i - (a*profile D k (cell h i) (elapsed dt K)+b)| ≤
      eps0 + |a| * ((D*h^2*k^4/12 + (D^2*h^2*k^6/12)*cap + (D^3*k^6/6)*cap^2)*T) := by
    rw [hev]
    have h2 := affine_error_bound a b (evolve D h dt w0 K i)
      (profile D k (cell h i) (elapsed dt K)) _ hcos
    have h3 : |a| * (eps0 / |a| + (D*h^2*k^4/12 + (D^2*h^2*k^6/12)*cap + (D^3*k^6/6)*cap^2)*T) =
        eps0 + |a| * ((D*h^2*k^4/12 + (D^2*h^2*k^6/12)*cap + (D^3*k^6/6)*cap^2)*T) := by
      first | (field_simp; ring) | field_simp
    linarith [h2, h3]
  have p1 := abs_le.mp hpert
  have p2 := abs_le.mp hexact
  apply abs_le.mpr
  constructor <;> linarith [p1.1, p1.2, p2.1, p2.2]

end heat_final

#print axioms heat_final.budget_const
#print axioms heat_final.perturbation_only
#print axioms heat_final.harness_error_bound
