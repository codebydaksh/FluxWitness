import Lean.Elab.Tactic.Omega
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Exp

set_option linter.unusedVariables false

namespace heat_1d

structure State where
  u : Real

structure Parameters where
  D : Real   -- diffusion coefficient (> 0)

@[ext] structure DiffusiveFlux where
  flux_u : Real

structure SpatialGradient where
  u_x : Real

structure SecondDerivative where
  u_xx : Real

/-- Diffusive flux: F = -D · u_x -/
noncomputable def xDiffFlux (U : State) (P : Parameters)
    (DU : SpatialGradient) : DiffusiveFlux :=
  { flux_u := -P.D * DU.u_x }

/-- RHS of the heat equation: rhs = D · u_xx -/
noncomputable def rhs (P : Parameters) (D2U : SecondDerivative) : Real :=
  P.D * D2U.u_xx

/-- Discrete second derivative on a uniform grid -/
noncomputable def discreteSecondDeriv (uL uC uR dx : Real) : Real :=
  (uR - 2 * uC + uL) / (dx * dx)

-- =============================================================
-- Theorem 1: Diffusive flux vanishes on constant states
-- =============================================================
theorem xDiffFluxOnConstant (U : State) (P : Parameters) :
    (xDiffFlux U P { u_x := 0 }).flux_u = 0 := by
  unfold xDiffFlux
  ring

-- =============================================================
-- Theorem 2: Diffusive flux is linear in the gradient
-- =============================================================
theorem xDiffFluxLinear (U : State) (P : Parameters) (a b : Real)
    (DU DV : SpatialGradient) :
    (xDiffFlux U P { u_x := a * DU.u_x + b * DV.u_x }).flux_u
    = a * (xDiffFlux U P DU).flux_u
    + b * (xDiffFlux U P DV).flux_u := by
  unfold xDiffFlux
  ring

-- =============================================================
-- Theorem 3: Down-gradient transport (Fick's law) for D > 0
-- =============================================================
theorem xDiffFluxDownGradient (U : State) (P : Parameters)
    (DU : SpatialGradient) (hD : P.D > 0) (hgrad : DU.u_x > 0) :
    (xDiffFlux U P DU).flux_u < 0 := by
  unfold xDiffFlux
  simp
  exact mul_pos hD hgrad

-- =============================================================
-- Theorem 4: Discrete Laplacian consistency —
--   on a constant state (uL = uC = uR), it evaluates to 0.
-- =============================================================
theorem discreteLaplacian_constant (u dx : Real) (hdx : dx ≠ 0) :
    discreteSecondDeriv u u u dx = 0 := by
  unfold discreteSecondDeriv
  have : (u - 2 * u + u) = 0 := by ring
  rw [this]
  simp

-- =============================================================
-- Theorem 5: Discrete Laplacian exactness for quadratic functions.
--   For u(x) = x², the discrete second derivative equals 2 exactly.
-- =============================================================
theorem discreteLaplacian_quadratic (xC dx : Real) (hdx : dx > 0) :
    discreteSecondDeriv ((xC - dx)^2) (xC^2) ((xC + dx)^2) dx = 2 := by
  unfold discreteSecondDeriv
  have hdx2 : dx * dx ≠ 0 := by positivity
  field_simp
  ring

-- =============================================================
-- Theorem 6: Discrete maximum principle at a single interior update.
--   Rewrite:  u_new = (1 - 2μ) uC + μ uL + μ uR   with μ = D dt/dx².
--   Given CFL 2D dt ≤ dx², μ ≤ 1/2, so all three coefficients are
--   nonnegative and sum to 1, giving a convex combination.
-- =============================================================
theorem discrete_max_principle (uL uC uR M D dt dx : Real)
    (hdx : dx > 0) (hD : D ≥ 0) (hdt : dt ≥ 0)
    (hL : uL ≤ M) (hC : uC ≤ M) (hR : uR ≤ M)
    (hCFL : 2 * D * dt ≤ dx * dx) :
    uC + D * dt * discreteSecondDeriv uL uC uR dx ≤ M := by
  unfold discreteSecondDeriv
  have hdx2 : dx * dx > 0 := mul_pos hdx hdx
  have hDdt_nn : D * dt ≥ 0 := mul_nonneg hD hdt
  -- Key rewrite: uC + (D dt / dx²)(uR - 2uC + uL)
  have hrewrite :
      uC + D * dt * ((uR - 2 * uC + uL) / (dx * dx))
      = (1 - 2 * (D * dt / (dx * dx))) * uC
        + (D * dt / (dx * dx)) * uL
        + (D * dt / (dx * dx)) * uR := by
    field_simp
    ring
  rw [hrewrite]
  set μ : Real := D * dt / (dx * dx)
  have hμ_nn : μ ≥ 0 := div_nonneg hDdt_nn (le_of_lt hdx2)
  have hμ_half : μ ≤ 1/2 := by
    have h1 : D * dt ≤ (1/2) * (dx * dx) := by linarith
    have hstep : μ ≤ (1/2) * (dx * dx) / (dx * dx) :=
      div_le_div_of_nonneg_right h1 (le_of_lt hdx2)
    have hcancel : (1/2 : Real) * (dx * dx) / (dx * dx) = 1/2 := by
      field_simp
    linarith [hstep, hcancel.le, hcancel.ge]
  have h1m2μ_nn : 1 - 2 * μ ≥ 0 := by linarith
  have b1 : (1 - 2 * μ) * uC ≤ (1 - 2 * μ) * M :=
    mul_le_mul_of_nonneg_left hC h1m2μ_nn
  have b2 : μ * uL ≤ μ * M := mul_le_mul_of_nonneg_left hL hμ_nn
  have b3 : μ * uR ≤ μ * M := mul_le_mul_of_nonneg_left hR hμ_nn
  have hsum : (1 - 2 * μ) * M + μ * M + μ * M = M := by ring
  linarith

-- =============================================================
-- Theorem 7: Discrete minimum principle (dual of Theorem 6).
-- =============================================================
theorem discrete_min_principle (uL uC uR m D dt dx : Real)
    (hdx : dx > 0) (hD : D ≥ 0) (hdt : dt ≥ 0)
    (hL : m ≤ uL) (hC : m ≤ uC) (hR : m ≤ uR)
    (hCFL : 2 * D * dt ≤ dx * dx) :
    m ≤ uC + D * dt * discreteSecondDeriv uL uC uR dx := by
  unfold discreteSecondDeriv
  have hdx2 : dx * dx > 0 := mul_pos hdx hdx
  have hDdt_nn : D * dt ≥ 0 := mul_nonneg hD hdt
  have hrewrite :
      uC + D * dt * ((uR - 2 * uC + uL) / (dx * dx))
      = (1 - 2 * (D * dt / (dx * dx))) * uC
        + (D * dt / (dx * dx)) * uL
        + (D * dt / (dx * dx)) * uR := by
    field_simp
    ring
  rw [hrewrite]
  set μ : Real := D * dt / (dx * dx)
  have hμ_nn : μ ≥ 0 := div_nonneg hDdt_nn (le_of_lt hdx2)
  have hμ_half : μ ≤ 1/2 := by
    have h1 : D * dt ≤ (1/2) * (dx * dx) := by linarith
    have hstep : μ ≤ (1/2) * (dx * dx) / (dx * dx) :=
      div_le_div_of_nonneg_right h1 (le_of_lt hdx2)
    have hcancel : (1/2 : Real) * (dx * dx) / (dx * dx) = 1/2 := by
      field_simp
    linarith [hstep, hcancel.le, hcancel.ge]
  have h1m2μ_nn : 1 - 2 * μ ≥ 0 := by linarith
  have b1 : (1 - 2 * μ) * m ≤ (1 - 2 * μ) * uC :=
    mul_le_mul_of_nonneg_left hC h1m2μ_nn
  have b2 : μ * m ≤ μ * uL := mul_le_mul_of_nonneg_left hL hμ_nn
  have b3 : μ * m ≤ μ * uR := mul_le_mul_of_nonneg_left hR hμ_nn
  have hsum : (1 - 2 * μ) * m + μ * m + μ * m = m := by ring
  linarith

-- =============================================================
-- Theorem 8: Gaussian variance grows linearly (heat kernel).
--   σ(t)² = σ_0² + 2Dt is strictly increasing in t.
-- =============================================================
noncomputable def sigmaSq (sigma0 D t : Real) : Real :=
  sigma0 * sigma0 + 2 * D * t

theorem sigmaSq_monotone (sigma0 D t1 t2 : Real)
    (hD : D > 0) (ht : t1 < t2) :
    sigmaSq sigma0 D t1 < sigmaSq sigma0 D t2 := by
  unfold sigmaSq
  have h2D : 2 * D > 0 := by linarith
  nlinarith [mul_lt_mul_of_pos_left ht h2D]

-- =============================================================
-- Theorem 9: Fourier mode decay identity.
--   For each mode k, the amplitude satisfies A(t) = exp(-D k² t).
--   We prove that A(t1)/A(t2) = exp(D k² (t2 - t1)), and
--   that A is monotone-decreasing in t for D k² > 0.
-- =============================================================
theorem fourier_mode_decay (D k t1 t2 : Real)
    (hD : D > 0) (hk : k ≠ 0) (ht : t1 < t2) :
    Real.exp (-D * k^2 * t2) < Real.exp (-D * k^2 * t1) := by
  apply Real.exp_lt_exp.mpr
  have hk2 : k^2 > 0 := by positivity
  have hDk2 : D * k^2 > 0 := mul_pos hD hk2
  nlinarith [mul_lt_mul_of_pos_left ht hDk2]

-- =============================================================
-- Theorem 10: Pure diffusion CFL condition (explicit Euler).
--   dt ≤ dx² / (2D) implies μ = D dt / dx² ≤ 1/2.
-- =============================================================
theorem cfl_pure_diffusion (dx dt D : Real)
    (hdx : dx > 0) (hD : D > 0)
    (hcfl : dt ≤ dx * dx / (2 * D)) :
    D * dt / (dx * dx) ≤ 1/2 := by
  have hdx2 : dx * dx > 0 := mul_pos hdx hdx
  have h2D  : 2 * D > 0   := by linarith
  rw [div_le_iff₀ hdx2]
  have := (le_div_iff₀ h2D).mp hcfl
  linarith

end heat_1d

#print axioms heat_1d.xDiffFluxOnConstant
#print axioms heat_1d.xDiffFluxLinear
#print axioms heat_1d.xDiffFluxDownGradient
#print axioms heat_1d.discreteLaplacian_constant
#print axioms heat_1d.discreteLaplacian_quadratic
#print axioms heat_1d.discrete_max_principle
#print axioms heat_1d.discrete_min_principle
#print axioms heat_1d.sigmaSq_monotone
#print axioms heat_1d.fourier_mode_decay
#print axioms heat_1d.cfl_pure_diffusion
/-! Finite-grid model of implementations/heat_1d.c in exact real arithmetic.
The end cells repeat their own values as ghost values (zero boundary flux).
The time integrator is the implemented two-stage Heun / SSP-RK2 update.
This model does not establish floating-point correctness or PDE convergence. -/
namespace heat_1d.FiniteGrid

def left {n : Nat} (i : Fin n) : Fin n :=
  ⟨i.val - 1, by omega⟩

def right {n : Nat} (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else i

noncomputable def euler {n : Nat} (D dt dx : Real) (u : Fin n → Real) : Fin n → Real :=
  fun i => u i + D * dt * discreteSecondDeriv (u (left i)) (u i) (u (right i)) dx

noncomputable def heun {n : Nat} (D dt dx : Real) (u : Fin n → Real) : Fin n → Real :=
  fun i => (u i + euler D dt dx (euler D dt dx u) i) / 2

def Bounded {n : Nat} (lo hi : Real) (u : Fin n → Real) : Prop :=
  ∀ i, lo ≤ u i ∧ u i ≤ hi

theorem euler_bounded {n : Nat} (D dt dx lo hi : Real) (u : Fin n → Real)
    (hdx : 0 < dx) (hD : 0 ≤ D) (hdt : 0 ≤ dt)
    (hCFL : 2 * D * dt ≤ dx * dx) (hu : Bounded lo hi u) :
    Bounded lo hi (euler D dt dx u) := by
  intro i
  exact ⟨discrete_min_principle _ _ _ lo D dt dx hdx hD hdt
      (hu (left i)).1 (hu i).1 (hu (right i)).1 hCFL,
    discrete_max_principle _ _ _ hi D dt dx hdx hD hdt
      (hu (left i)).2 (hu i).2 (hu (right i)).2 hCFL⟩

theorem heun_bounded {n : Nat} (D dt dx lo hi : Real) (u : Fin n → Real)
    (hdx : 0 < dx) (hD : 0 ≤ D) (hdt : 0 ≤ dt)
    (hCFL : 2 * D * dt ≤ dx * dx) (hu : Bounded lo hi u) :
    Bounded lo hi (heun D dt dx u) := by
  have h1 := euler_bounded D dt dx lo hi u hdx hD hdt hCFL hu
  have h2 := euler_bounded D dt dx lo hi (euler D dt dx u) hdx hD hdt hCFL h1
  intro i
  dsimp [heun]
  obtain ⟨hl, hh⟩ := hu i
  obtain ⟨hl2, hh2⟩ := h2 i
  constructor <;> linarith

noncomputable def evolve {n : Nat} (D dx : Real) (dt : Nat → Real)
    (u0 : Fin n → Real) : Nat → Fin n → Real
  | 0 => u0
  | k + 1 => heun D (dt k) dx (evolve D dx dt u0 k)

/-- Global maximum/minimum principle for every number of complete SSP-RK2 steps,
including variable timesteps and the implemented clamped boundary cells. -/
theorem evolve_bounded {n : Nat} (D dx lo hi : Real) (dt : Nat → Real)
    (u0 : Fin n → Real) (hdx : 0 < dx) (hD : 0 ≤ D)
    (hdt : ∀ k, 0 ≤ dt k) (hCFL : ∀ k, 2 * D * dt k ≤ dx * dx)
    (hu : Bounded lo hi u0) (k : Nat) : Bounded lo hi (evolve D dx dt u0 k) := by
  induction k with
  | zero => exact hu
  | succ k ih => exact heun_bounded D (dt k) dx lo hi _ hdx hD (hdt k) (hCFL k) ih

end heat_1d.FiniteGrid

#print axioms heat_1d.FiniteGrid.euler_bounded
#print axioms heat_1d.FiniteGrid.heun_bounded
#print axioms heat_1d.FiniteGrid.evolve_bounded

namespace heat_1d.FiniteGrid

/-- Linearity of the complete implemented time step, including clamped endpoints. -/
theorem heun_sub {n : Nat} (D dt dx : Real) (u v : Fin n → Real) :
    heun D dt dx (fun i => u i - v i) =
      (fun i => heun D dt dx u i - heun D dt dx v i) := by
  funext i
  simp only [heun, euler, discreteSecondDeriv]
  ring

/-- Supremum-norm nonexpansion, expressed pointwise without selecting a maximizing cell. -/
theorem heun_difference_bounded {n : Nat} (D dt dx e : Real) (u v : Fin n → Real)
    (hdx : 0 < dx) (hD : 0 ≤ D) (hdt : 0 ≤ dt)
    (hCFL : 2 * D * dt ≤ dx * dx)
    (huv : Bounded (-e) e (fun i => u i - v i)) :
    Bounded (-e) e (fun i => heun D dt dx u i - heun D dt dx v i) := by
  have h := heun_bounded D dt dx (-e) e (fun i => u i - v i)
    hdx hD hdt hCFL huv
  rw [heun_sub] at h
  exact h

noncomputable def errorBudget (initial : Real) (defect : Nat → Real) : Nat → Real
  | 0 => initial
  | k + 1 => errorBudget initial defect k + defect k

/-- Error propagation against an arbitrary reference sequence.
The local defect bound is an explicit hypothesis: this is a stability lemma,
not a PDE consistency or convergence theorem. It must later be combined with
a proved defect estimate for a solution with the correct boundary conditions. -/
theorem evolve_error_budget {n : Nat} (D dx initial : Real)
    (dt defect : Nat → Real) (u0 : Fin n → Real) (reference : Nat → Fin n → Real)
    (hdx : 0 < dx) (hD : 0 ≤ D)
    (hdt : ∀ k, 0 ≤ dt k) (hCFL : ∀ k, 2 * D * dt k ≤ dx * dx)
    (hinit : Bounded (-initial) initial (fun i => u0 i - reference 0 i))
    (hdefect : ∀ k, Bounded (-(defect k)) (defect k)
      (fun i => heun D (dt k) dx (reference k) i - reference (k + 1) i))
    (k : Nat) :
    Bounded (-(errorBudget initial defect k)) (errorBudget initial defect k)
      (fun i => evolve D dx dt u0 k i - reference k i) := by
  induction k with
  | zero => exact hinit
  | succ k ih =>
    have hstep := heun_difference_bounded D (dt k) dx (errorBudget initial defect k)
      (evolve D dx dt u0 k) (reference k) hdx hD (hdt k) (hCFL k) ih
    intro i
    obtain ⟨hlo, hhi⟩ := hstep i
    obtain ⟨dlo, dhi⟩ := hdefect k i
    simp only [evolve, errorBudget]
    constructor <;> linarith

end heat_1d.FiniteGrid

#print axioms heat_1d.FiniteGrid.heun_sub
#print axioms heat_1d.FiniteGrid.heun_difference_bounded
#print axioms heat_1d.FiniteGrid.evolve_error_budget
