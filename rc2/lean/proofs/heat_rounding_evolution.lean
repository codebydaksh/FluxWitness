import proofs.heat_rounding_grid_bridge
import proofs.heat_range_bootstrap

/-! Abstract rounded evolution, not C execution. LocalArithmetic's laws are
explicit assumptions; the native implementation has not been proved to satisfy
this update. The comparison starts from the same initial array on both sides. -/
namespace heat_rounding
noncomputable section
open heat_1d.FiniteGrid

def roundingDelta : Real := 271/100000000000000000

def roundedStencil (a : LocalArithmetic) (l c r D q : Real) : Real :=
  a.round (D * a.round (a.round (a.round (r-2*c)+l)/q))

def roundedEuler (a : LocalArithmetic) (l c r dt D q : Real) : Real :=
  a.round (c + a.round (dt * roundedStencil a l c r D q))

def roundedStep {n : Nat} (a : LocalArithmetic) (D dt q : Real)
    (u : Fin n → Real) (i : Fin n) : Real :=
  let stage := fun j => roundedEuler a (u (left j)) (u j) (u (right j)) dt D q
  let finalStage := roundedEuler a (stage (left i)) (stage i) (stage (right i)) dt D q
  a.round (a.half (u i) + a.half finalStage)

theorem benchmarkGrid_computed {n : Nat} (a : LocalArithmetic)
    (u : Fin n → Real) (hu : ∀ i, |u i| ≤ 2)
    (dt : Real) (hdt : |dt| ≤ 9/2000) (i : Fin n) :
    (benchmarkGrid a u hu dt hdt i).computedValue =
      roundedStep a storedD dt storedQ u i := by
  rfl

theorem roundedStep_perturbation {n : Nat} (a : LocalArithmetic)
    (ha : a.unit = 1/9007199254740992) (he : a.allowance = 1/10^30)
    (u : Fin n → Real) (hu : Bounded (-2) 2 u)
    (dt : Real) (hdt : |dt| ≤ 9/2000) (h : Real) (hh : h ≠ 0) :
    Bounded (-roundingDelta) roundingDelta
      (fun i => roundedStep a storedD dt storedQ u i -
        heun (effectiveDiffusivity storedD h storedQ) dt h u i) := by
  have hu' : ∀ i, |u i| ≤ 2 := fun i => abs_le.mpr (hu i)
  intro i
  have hb := grid_rounding_bound a ha he u hu' dt hdt h hh i
  rw [benchmarkGrid_computed] at hb
  exact abs_le.mp hb

def roundedEvolution {n : Nat} (a : LocalArithmetic) (dt : Nat → Real)
    (u0 : Fin n → Real) : Nat → Fin n → Real
  | 0 => u0
  | k+1 => roundedStep a storedD (dt k) storedQ (roundedEvolution a dt u0 k)

/-- No per-step perturbation hypothesis is supplied: it is derived from the
abstract arithmetic laws above. Range closure is proved by induction. This is
rounding accumulation relative to the exact scheme, not the analytic PDE error. -/
theorem roundedEvolution_error_and_range {n : Nat} (a : LocalArithmetic)
    (ha : a.unit = 1/9007199254740992) (he : a.allowance = 1/10^30)
    (h M : Real) (hh : 0 < h) (dt : Nat → Real) (u0 : Fin n → Real) (K : Nat)
    (ht : ∀ k, 0 ≤ dt k) (hcap : ∀ k, |dt k| ≤ 9/2000)
    (hCFL : ∀ k, 2*effectiveDiffusivity storedD h storedQ*dt k ≤ h*h)
    (hu0 : Bounded (-M) M u0) (hmargin : M+(K:Real)*roundingDelta ≤ 2) :
    ∀ j, j ≤ K →
      Bounded (-((j:Real)*roundingDelta)) ((j:Real)*roundingDelta)
        (fun i => roundedEvolution a dt u0 j i -
          evolve (effectiveDiffusivity storedD h storedQ) h dt u0 j i) ∧
      Bounded (-2) 2 (roundedEvolution a dt u0 j) := by
  have hD : 0 ≤ effectiveDiffusivity storedD h storedQ :=
    effectiveDiffusivity_nonnegative _ _ _ (by norm_num [storedD]) (le_of_lt storedQ_pos)
  have hb := finite_range_bootstrap
    (effectiveDiffusivity storedD h storedQ) h 0 roundingDelta M 2 dt
    (roundedEvolution a dt u0)
    (fun j => evolve (effectiveDiffusivity storedD h storedQ) h dt u0 j) K
    hh hD (by norm_num [roundingDelta])
    (fun j _ => ht j) (fun j _ => hCFL j)
    (by intro j _; rfl)
    (by intro j _; exact evolve_bounded _ _ _ _ _ _ hh hD ht hCFL hu0 j)
    (by intro i; simp [roundedEvolution, evolve])
    (by simpa using hmargin)
    (by
      intro j _ hr
      exact roundedStep_perturbation a ha he (roundedEvolution a dt u0 j) hr
        (dt j) (hcap j) h (ne_of_gt hh))
  simpa using hb

end
end heat_rounding
