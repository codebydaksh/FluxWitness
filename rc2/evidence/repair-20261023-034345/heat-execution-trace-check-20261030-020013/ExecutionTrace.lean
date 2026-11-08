import PDEAudit
import proofs.heat_rounding_evolution

/-! Conditional execution-trace interface. `trace` is not defined to be the
model recurrence. A caller must supply its initial-state and one-step
correspondence, including any native execution/memory/parameter obligations.
Those obligations are NOT proved by this module. The step correspondence is
required only on bounded inputs; the range is derived, not assumed for trace. -/
namespace heat_rounding
open heat_1d.FiniteGrid

theorem trace_eq_roundedEvolution_of_bounded_step {n : Nat}
    (a : LocalArithmetic) (dt : Nat → Real) (u0 : Fin n → Real)
    (trace : Nat → Fin n → Real) (K : Nat)
    (hinit : trace 0 = u0)
    (hmodel : ∀ j, j ≤ K → Bounded (-2) 2 (roundedEvolution a dt u0 j))
    (hstep : ∀ j, j < K → Bounded (-2) 2 (trace j) →
      trace (j+1) = roundedStep a storedD (dt j) storedQ (trace j)) :
    ∀ j, j ≤ K → trace j = roundedEvolution a dt u0 j := by
  intro j
  induction j with
  | zero => intro _; exact hinit
  | succ j ih =>
    intro hj
    have hjK : j ≤ K := Nat.le_trans (Nat.le_succ j) hj
    have heq := ih hjK
    have hr : Bounded (-2) 2 (trace j) := by
      rw [heq]
      exact hmodel j hjK
    rw [hstep j (Nat.lt_of_succ_le hj) hr, heq]
    rfl

/-- Transfer the proved model's range and error budget to a separately supplied
trace. No IEEE/C conformance is inferred from the trace's name or type. -/
theorem trace_error_and_range {n : Nat} (a : LocalArithmetic)
    (ha : a.unit = 1/9007199254740992) (he : a.allowance = 1/10^30)
    (h M : Real) (hh : 0 < h) (dt : Nat → Real) (u0 : Fin n → Real) (K : Nat)
    (ht : ∀ k, 0 ≤ dt k) (hcap : ∀ k, |dt k| ≤ 9/2000)
    (hCFL : ∀ k, 2*effectiveDiffusivity storedD h storedQ*dt k ≤ h*h)
    (hu0 : Bounded (-M) M u0) (hmargin : M+(K:Real)*roundingDelta ≤ 2)
    (trace : Nat → Fin n → Real) (hinit : trace 0 = u0)
    (hstep : ∀ j, j < K → Bounded (-2) 2 (trace j) →
      trace (j+1) = roundedStep a storedD (dt j) storedQ (trace j)) :
    ∀ j, j ≤ K →
      Bounded (-((j:Real)*roundingDelta)) ((j:Real)*roundingDelta)
        (fun i => trace j i -
          evolve (effectiveDiffusivity storedD h storedQ) h dt u0 j i) ∧
      Bounded (-2) 2 (trace j) := by
  have hm := roundedEvolution_error_and_range a ha he h M hh dt u0 K
    ht hcap hCFL hu0 hmargin
  have htmodel := trace_eq_roundedEvolution_of_bounded_step a dt u0 trace K
    hinit (fun j hj => (hm j hj).2) hstep
  intro j hj
  rw [htmodel j hj]
  exact hm j hj

end heat_rounding

#audit_local_declarations
