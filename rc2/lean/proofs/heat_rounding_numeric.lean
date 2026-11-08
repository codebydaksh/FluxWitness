import proofs.heat_rounding_certificate

/-! Numerical instantiation of the abstract scalar certificates.
The local error allowance 10^-30 deliberately exceeds binary64 subnormal
rounding error; no theorem here establishes machine adherence to that law.
The coefficients below are exact rational values of the stored binary64 D and q.
-/
namespace heat_rounding
noncomputable section
set_option maxHeartbeats 2000000

def storedD : Real := 5764607523034235 / 576460752303423488
def storedQ : Real := 4150517416584649 / 18446744073709551616
theorem storedQ_pos : 0 < storedQ := by norm_num [storedQ]

def sampleInput (u : Fin 5 → Real) (hu : ∀ i, |u i| ≤ 2) (i : Fin 5) :=
  ScalarCertificate.input (u i) 2 (hu i)

def benchmarkInterior (a : LocalArithmetic)
    (u : Fin 5 → Real) (hu : ∀ i, |u i| ≤ 2)
    (dt : Real) (hdt : |dt| ≤ 9/2000) : ScalarCertificate :=
  heunInteriorCertificate a (sampleInput u hu 0) (sampleInput u hu 1) (sampleInput u hu 2) (sampleInput u hu 3) (sampleInput u hu 4)
    (ScalarCertificate.input dt (9/2000) hdt) storedD storedQ storedQ_pos

theorem interior_numeric_budget (a : LocalArithmetic)
    (ha : a.unit = 1/9007199254740992) (he : a.allowance = 1/10^30)
    (u : Fin 5 → Real) (hu : ∀ i, |u i| ≤ 2)
    (dt : Real) (hdt : |dt| ≤ 9/2000) :
    (benchmarkInterior a u hu dt hdt).error ≤ 271/100000000000000000 := by
  norm_num [benchmarkInterior, heunInteriorCertificate, eulerCertificate, stencilCertificate,
    ScalarCertificate.add, ScalarCertificate.sub, ScalarCertificate.mul,
    ScalarCertificate.divConst, ScalarCertificate.rounded, ScalarCertificate.double,
    ScalarCertificate.halved, ScalarCertificate.constant, ScalarCertificate.input,
    sampleInput, storedD, storedQ, ha, he]

theorem interior_rounding_bound (a : LocalArithmetic)
    (ha : a.unit = 1/9007199254740992) (he : a.allowance = 1/10^30)
    (u : Fin 5 → Real) (hu : ∀ i, |u i| ≤ 2)
    (dt : Real) (hdt : |dt| ≤ 9/2000) :
    |(benchmarkInterior a u hu dt hdt).computedValue -
      (benchmarkInterior a u hu dt hdt).exactValue| ≤ 271/100000000000000000 :=
  le_trans (benchmarkInterior a u hu dt hdt).valid.error
    (interior_numeric_budget a ha he u hu dt hdt)

def benchmarkLeft (a : LocalArithmetic)
    (u : Fin 5 → Real) (hu : ∀ i, |u i| ≤ 2)
    (dt : Real) (hdt : |dt| ≤ 9/2000) : ScalarCertificate :=
  heunLeftCertificate a (sampleInput u hu 0) (sampleInput u hu 1) (sampleInput u hu 2)
    (ScalarCertificate.input dt (9/2000) hdt) storedD storedQ storedQ_pos

theorem left_numeric_budget (a : LocalArithmetic)
    (ha : a.unit = 1/9007199254740992) (he : a.allowance = 1/10^30)
    (u : Fin 5 → Real) (hu : ∀ i, |u i| ≤ 2)
    (dt : Real) (hdt : |dt| ≤ 9/2000) :
    (benchmarkLeft a u hu dt hdt).error ≤ 271/100000000000000000 := by
  norm_num [benchmarkLeft, heunLeftCertificate, eulerCertificate, stencilCertificate,
    ScalarCertificate.add, ScalarCertificate.sub, ScalarCertificate.mul,
    ScalarCertificate.divConst, ScalarCertificate.rounded, ScalarCertificate.double,
    ScalarCertificate.halved, ScalarCertificate.constant, ScalarCertificate.input,
    sampleInput, storedD, storedQ, ha, he]

theorem left_rounding_bound (a : LocalArithmetic)
    (ha : a.unit = 1/9007199254740992) (he : a.allowance = 1/10^30)
    (u : Fin 5 → Real) (hu : ∀ i, |u i| ≤ 2)
    (dt : Real) (hdt : |dt| ≤ 9/2000) :
    |(benchmarkLeft a u hu dt hdt).computedValue -
      (benchmarkLeft a u hu dt hdt).exactValue| ≤ 271/100000000000000000 :=
  le_trans (benchmarkLeft a u hu dt hdt).valid.error
    (left_numeric_budget a ha he u hu dt hdt)

def benchmarkRight (a : LocalArithmetic)
    (u : Fin 5 → Real) (hu : ∀ i, |u i| ≤ 2)
    (dt : Real) (hdt : |dt| ≤ 9/2000) : ScalarCertificate :=
  heunRightCertificate a (sampleInput u hu 2) (sampleInput u hu 3) (sampleInput u hu 4)
    (ScalarCertificate.input dt (9/2000) hdt) storedD storedQ storedQ_pos

theorem right_numeric_budget (a : LocalArithmetic)
    (ha : a.unit = 1/9007199254740992) (he : a.allowance = 1/10^30)
    (u : Fin 5 → Real) (hu : ∀ i, |u i| ≤ 2)
    (dt : Real) (hdt : |dt| ≤ 9/2000) :
    (benchmarkRight a u hu dt hdt).error ≤ 271/100000000000000000 := by
  norm_num [benchmarkRight, heunRightCertificate, eulerCertificate, stencilCertificate,
    ScalarCertificate.add, ScalarCertificate.sub, ScalarCertificate.mul,
    ScalarCertificate.divConst, ScalarCertificate.rounded, ScalarCertificate.double,
    ScalarCertificate.halved, ScalarCertificate.constant, ScalarCertificate.input,
    sampleInput, storedD, storedQ, ha, he]

theorem right_rounding_bound (a : LocalArithmetic)
    (ha : a.unit = 1/9007199254740992) (he : a.allowance = 1/10^30)
    (u : Fin 5 → Real) (hu : ∀ i, |u i| ≤ 2)
    (dt : Real) (hdt : |dt| ≤ 9/2000) :
    |(benchmarkRight a u hu dt hdt).computedValue -
      (benchmarkRight a u hu dt hdt).exactValue| ≤ 271/100000000000000000 :=
  le_trans (benchmarkRight a u hu dt hdt).valid.error
    (right_numeric_budget a ha he u hu dt hdt)

end
end heat_rounding

