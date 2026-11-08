import proofs.heat_rounding_operations

/-! Proof-carrying scalar evaluation under explicit rounding laws.
This is an abstract arithmetic model, not an IEEE or C semantics. In particular,
the global laws below must not be asserted for overflowing machine operations.
Actual machine use requires establishing these laws on all reachable operands.
-/
namespace heat_rounding

noncomputable section

structure ScalarCertificate where
  exactValue : Real
  computedValue : Real
  magnitude : Real
  error : Real
  valid : ErrorBound exactValue computedValue magnitude error

structure LocalArithmetic where
  unit : Real
  allowance : Real
  unit_nonneg : 0 ≤ unit
  round : Real → Real
  round_law : ∀ x, |round x - x| ≤ unit * |x| + allowance
  half : Real → Real
  half_law : ∀ x, |half x - x/2| ≤ allowance

def ScalarCertificate.input (x M : Real) (hx : |x| ≤ M) : ScalarCertificate :=
  ⟨x, x, M, 0, ⟨hx, by simp⟩⟩

def ScalarCertificate.constant (x : Real) : ScalarCertificate :=
  ScalarCertificate.input x |x| (le_refl _)

def ScalarCertificate.rounded (a : LocalArithmetic) (x : ScalarCertificate) :
    ScalarCertificate where
  exactValue := x.exactValue
  computedValue := a.round x.computedValue
  magnitude := x.magnitude
  error := x.error + a.unit * (x.magnitude + x.error) + a.allowance
  valid := ErrorBound.round _ _ _ _ _ _ _ x.valid a.unit_nonneg (a.round_law _)

def ScalarCertificate.add (a : LocalArithmetic) (x y : ScalarCertificate) :
    ScalarCertificate :=
  ScalarCertificate.rounded a
    ⟨x.exactValue+y.exactValue, x.computedValue+y.computedValue,
      x.magnitude+y.magnitude, x.error+y.error,
      ErrorBound.add _ _ _ _ _ _ _ _ x.valid y.valid⟩

def ScalarCertificate.sub (a : LocalArithmetic) (x y : ScalarCertificate) :
    ScalarCertificate :=
  ScalarCertificate.rounded a
    ⟨x.exactValue-y.exactValue, x.computedValue-y.computedValue,
      x.magnitude+y.magnitude, x.error+y.error,
      ErrorBound.sub _ _ _ _ _ _ _ _ x.valid y.valid⟩

def ScalarCertificate.mul (a : LocalArithmetic) (x y : ScalarCertificate) :
    ScalarCertificate :=
  ScalarCertificate.rounded a
    ⟨x.exactValue*y.exactValue, x.computedValue*y.computedValue,
      x.magnitude*y.magnitude,
      x.magnitude*y.error+y.magnitude*x.error+x.error*y.error,
      ErrorBound.mul _ _ _ _ _ _ _ _ x.valid y.valid⟩

def ScalarCertificate.divConst (a : LocalArithmetic) (x : ScalarCertificate)
    (q : Real) (hq : 0 < q) : ScalarCertificate :=
  ScalarCertificate.rounded a
    ⟨x.exactValue/q, x.computedValue/q, x.magnitude/q, x.error/q,
      ErrorBound.div_const _ _ _ _ _ x.valid hq⟩

/-- Exact doubling in this abstract model. Machine use must exclude overflow
and justify the power-of-two scaling correspondence. -/
def ScalarCertificate.double (x : ScalarCertificate) : ScalarCertificate where
  exactValue := 2*x.exactValue
  computedValue := 2*x.computedValue
  magnitude := 2*x.magnitude
  error := 2*x.error
  valid := by
    have h := ErrorBound.mul 2 x.exactValue 2 x.computedValue 2 x.magnitude 0 x.error
      (show ErrorBound 2 2 2 0 from ⟨by norm_num, by simp⟩) x.valid
    simpa using h

def ScalarCertificate.halved (a : LocalArithmetic) (x : ScalarCertificate) :
    ScalarCertificate where
  exactValue := x.exactValue/2
  computedValue := a.half x.computedValue
  magnitude := x.magnitude/2
  error := x.error/2+a.allowance
  valid := by
    have h := ErrorBound.div_const _ _ _ _ 2 x.valid (by norm_num)
    refine ⟨h.magnitude, ?_⟩
    have he := compose_error _ _ _ _ _ h.error (a.half_law x.computedValue)
    simpa [add_comm] using he

/-- C-order stencil expression under the abstract local arithmetic laws.
No numerical 2.71e-15 bound or C correspondence is claimed by this definition. -/
def stencilCertificate (a : LocalArithmetic) (left centre right : ScalarCertificate)
    (D q : Real) (hq : 0 < q) : ScalarCertificate :=
  let twice := ScalarCertificate.double centre
  let numerator := ScalarCertificate.add a (ScalarCertificate.sub a right twice) left
  ScalarCertificate.mul a (ScalarCertificate.constant D)
    (ScalarCertificate.divConst a numerator q hq)

def eulerCertificate (a : LocalArithmetic) (left centre right dt : ScalarCertificate)
    (D q : Real) (hq : 0 < q) : ScalarCertificate :=
  ScalarCertificate.add a centre
    (ScalarCertificate.mul a dt (stencilCertificate a left centre right D q hq))

/-- Interior Heun expression. Boundary cells must reuse the appropriate clamped
stage values; they are not established merely by this interior construction. -/
def heunInteriorCertificate (a : LocalArithmetic)
    (ll l c r rr dt : ScalarCertificate) (D q : Real) (hq : 0 < q) : ScalarCertificate :=
  let vl := eulerCertificate a ll l c dt D q hq
  let vc := eulerCertificate a l c r dt D q hq
  let vr := eulerCertificate a c r rr dt D q hq
  let finalStage := eulerCertificate a vl vc vr dt D q hq
  ScalarCertificate.add a
    (ScalarCertificate.halved a c)
    (ScalarCertificate.halved a finalStage)

/-- Left endpoint with the computed left stage reused for the clamped neighbor. -/
def heunLeftCertificate (a : LocalArithmetic)
    (p qv r dt : ScalarCertificate) (D q : Real) (hq : 0 < q) : ScalarCertificate :=
  let v0 := eulerCertificate a p p qv dt D q hq
  let v1 := eulerCertificate a p qv r dt D q hq
  let finalStage := eulerCertificate a v0 v0 v1 dt D q hq
  ScalarCertificate.add a (ScalarCertificate.halved a p)
    (ScalarCertificate.halved a finalStage)

/-- Right endpoint with the computed right stage reused for the clamped neighbor. -/
def heunRightCertificate (a : LocalArithmetic)
    (p qv r dt : ScalarCertificate) (D q : Real) (hq : 0 < q) : ScalarCertificate :=
  let v0 := eulerCertificate a p qv r dt D q hq
  let v1 := eulerCertificate a qv r r dt D q hq
  let finalStage := eulerCertificate a v0 v1 v1 dt D q hq
  ScalarCertificate.add a (ScalarCertificate.halved a r)
    (ScalarCertificate.halved a finalStage)

end
end heat_rounding
