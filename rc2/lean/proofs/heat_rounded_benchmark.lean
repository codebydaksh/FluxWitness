import proofs.heat_rounding_evolution
import proofs.heat_benchmark

/-! Candidate corollary for the explicit abstract rounded update. Not a theorem
about C execution: LocalArithmetic conformance and the initial-data error bound
remain external obligations. The reference uses effective diffusivity, not an
unaccounted substitution of the physical decimal diffusion coefficient. -/
namespace heat_rounding
open heat_1d.FiniteGrid heat_grid_bridge heat_reference

theorem abstract_rounded_benchmark
    (a : LocalArithmetic)
    (ha : a.unit = 1/9007199254740992) (he : a.allowance = 1/10^30)
    (D h k dt eps0 : Real) (u0 : Fin 400 → Real)
    (hD_eq : D = effectiveDiffusivity storedD h storedQ)
    (hh0 : (149999999999999994 / 10000000000000000000 : Real) ≤ h)
    (hh1 : h ≤ (3/200 : Real))
    (hD0 : 0 ≤ D)
    (hD1 : D ≤ (100000000000000011 / 10000000000000000000 : Real))
    (hdt0 : 0 ≤ dt)
    (hdt1 : dt ≤ (44843049327354261 / 10000000000000000000 : Real))
    (hk : k * (((400 : Nat) : Real)*h) = Real.pi)
    (heps0 : 0 ≤ eps0)
    (heps1 : eps0 ≤ (24854 / 100000000000000000000 : Real))
    (hinit : ∀ i, |u0 i - (1/2 * Real.cos (k*cell h i)+1)| ≤ eps0)
    (i : Fin 400) :
    |roundedEvolution a (fun _ => dt) u0 223 i -
      (1/2 * profile D k (cell h i) (((223 : Nat) : Real)*dt)+1)| ≤
      (705 / 100000000000 : Real) := by
  have hh : h ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hh0)
  have hcap : |dt| ≤ (9/2000 : Real) := by
    rw [abs_of_nonneg hdt0]
    linarith
  apply heat_benchmark.benchmark_n400 D h k dt eps0 roundingDelta
    (roundedEvolution a (fun _ => dt) u0)
    hh0 hh1 hD0 hD1 hdt0 hdt1 hk heps0 heps1
    (by norm_num [roundingDelta]) (by norm_num [roundingDelta])
    (by simpa only [roundedEvolution] using hinit) ?_ i
  intro j _ hr
  have hr' : Bounded (-2) 2 (roundedEvolution a (fun _ => dt) u0 j) :=
    fun i => abs_le.mp (hr i)
  have hb := roundedStep_perturbation a ha he
    (roundedEvolution a (fun _ => dt) u0 j) hr' dt hcap h hh
  rw [← hD_eq] at hb
  exact hb

end heat_rounding
