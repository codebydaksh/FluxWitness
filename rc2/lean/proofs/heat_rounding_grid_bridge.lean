import proofs.heat_rounding_numeric
import proofs.heat_stored_parameter_bridge

/-! Exact-value bridge only. The computed values use abstract arithmetic laws;
no C execution or binary64 correspondence is established by this module. -/
namespace heat_rounding
noncomputable section

theorem eulerCertificate_exact (a : LocalArithmetic)
    (l c r dt : ScalarCertificate) (D q : Real) (hq : 0 < q) :
    (eulerCertificate a l c r dt D q hq).exactValue =
      c.exactValue + dt.exactValue *
        (D * ((r.exactValue - 2*c.exactValue + l.exactValue)/q)) := by
  rfl

/-- The same clamped neighbor functions as the existing finite-grid scheme.
Stage values are reused at endpoints, as required by the two-stage update. -/
def gridCertificate {n : Nat} (a : LocalArithmetic)
    (u : Fin n → ScalarCertificate) (dt : ScalarCertificate)
    (D q : Real) (hq : 0 < q) (i : Fin n) : ScalarCertificate :=
  let stage := fun j => eulerCertificate a
    (u (heat_1d.FiniteGrid.left j)) (u j) (u (heat_1d.FiniteGrid.right j)) dt D q hq
  let finalStage := eulerCertificate a
    (stage (heat_1d.FiniteGrid.left i)) (stage i) (stage (heat_1d.FiniteGrid.right i)) dt D q hq
  ScalarCertificate.add a (ScalarCertificate.halved a (u i))
    (ScalarCertificate.halved a finalStage)

theorem gridCertificate_exact {n : Nat} (a : LocalArithmetic)
    (u : Fin n → ScalarCertificate) (dt : ScalarCertificate)
    (D q : Real) (hq : 0 < q) (i : Fin n) :
    (gridCertificate a u dt D q hq i).exactValue =
      heat_1d.FiniteGrid.storedHeun D dt.exactValue q (fun j => (u j).exactValue) i := by
  simp only [gridCertificate, ScalarCertificate.add, ScalarCertificate.rounded,
    ScalarCertificate.halved, eulerCertificate_exact,
    heat_1d.FiniteGrid.storedHeun, heat_1d.FiniteGrid.storedEuler]
  ring

/-- Connect the certificate's error to the already analyzed real grid scheme,
using effective diffusivity to account for the separately stored denominator. -/
theorem gridCertificate_error {n : Nat} (a : LocalArithmetic)
    (u : Fin n → ScalarCertificate) (dt : ScalarCertificate)
    (D h q : Real) (hh : h ≠ 0) (hq : 0 < q) (i : Fin n) :
    |(gridCertificate a u dt D q hq i).computedValue -
      heat_1d.FiniteGrid.heun (heat_1d.FiniteGrid.effectiveDiffusivity D h q)
        dt.exactValue h (fun j => (u j).exactValue) i| ≤
      (gridCertificate a u dt D q hq i).error := by
  have hb := (gridCertificate a u dt D q hq i).valid.error
  rw [gridCertificate_exact,
    heat_1d.FiniteGrid.storedHeun_eq D dt.exactValue h q _ hh (ne_of_gt hq)] at hb
  exact hb

def benchmarkGrid {n : Nat} (a : LocalArithmetic)
    (u : Fin n → Real) (hu : ∀ i, |u i| ≤ 2)
    (dt : Real) (hdt : |dt| ≤ 9/2000) (i : Fin n) : ScalarCertificate :=
  gridCertificate a (fun j => ScalarCertificate.input (u j) 2 (hu j))
    (ScalarCertificate.input dt (9/2000) hdt) storedD storedQ storedQ_pos i

theorem grid_numeric_budget {n : Nat} (a : LocalArithmetic)
    (ha : a.unit = 1/9007199254740992) (he : a.allowance = 1/10^30)
    (u : Fin n → Real) (hu : ∀ i, |u i| ≤ 2)
    (dt : Real) (hdt : |dt| ≤ 9/2000) (i : Fin n) :
    (benchmarkGrid a u hu dt hdt i).error ≤ 271/100000000000000000 := by
  norm_num [benchmarkGrid, gridCertificate, eulerCertificate, stencilCertificate,
    ScalarCertificate.add, ScalarCertificate.sub, ScalarCertificate.mul,
    ScalarCertificate.divConst, ScalarCertificate.rounded, ScalarCertificate.double,
    ScalarCertificate.halved, ScalarCertificate.constant, ScalarCertificate.input,
    storedD, storedQ, ha, he]

/-- Per-step real-scheme perturbation bound under explicit abstract arithmetic
laws. The stored coefficients are fixed; the array size may be any natural.
This does not assert that an actual C array follows `benchmarkGrid`. -/
theorem grid_rounding_bound {n : Nat} (a : LocalArithmetic)
    (ha : a.unit = 1/9007199254740992) (he : a.allowance = 1/10^30)
    (u : Fin n → Real) (hu : ∀ i, |u i| ≤ 2)
    (dt : Real) (hdt : |dt| ≤ 9/2000) (h : Real) (hh : h ≠ 0) (i : Fin n) :
    |(benchmarkGrid a u hu dt hdt i).computedValue -
      heat_1d.FiniteGrid.heun (heat_1d.FiniteGrid.effectiveDiffusivity storedD h storedQ)
        dt h u i| ≤ 271/100000000000000000 := by
  have hb := gridCertificate_error a
    (fun j => ScalarCertificate.input (u j) 2 (hu j))
    (ScalarCertificate.input dt (9/2000) hdt) storedD h storedQ hh storedQ_pos i
  have hn := grid_numeric_budget a ha he u hu dt hdt i
  exact le_trans hb hn

end
end heat_rounding
