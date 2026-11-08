import proofs.heat_rounding_composition

/-! Compositional magnitude/error certificates for scalar arithmetic.
The local relative-plus-absolute rounding law is an explicit premise for each
operation. These results do not define IEEE arithmetic or certify C execution.
-/
namespace heat_rounding

/-- The exact value has magnitude at most `M`; its approximation has error at most `E`. -/
structure ErrorBound (value approx M E : Real) : Prop where
  magnitude : |value| ≤ M
  error : |approx - value| ≤ E

theorem ErrorBound.round (x input computed M E unit allowance : Real)
    (h : ErrorBound x input M E) (hu : 0 ≤ unit)
    (hr : |computed - input| ≤ unit * |input| + allowance) :
    ErrorBound x computed M (E + unit * (M + E) + allowance) :=
  ⟨h.magnitude, round_after_error x input computed E M unit allowance hu h.error h.magnitude hr⟩

theorem ErrorBound.add (x y xh yh Mx My Ex Ey : Real)
    (hx : ErrorBound x xh Mx Ex) (hy : ErrorBound y yh My Ey) :
    ErrorBound (x+y) (xh+yh) (Mx+My) (Ex+Ey) := by
  constructor
  · exact le_trans (abs_add_le x y) (add_le_add hx.magnitude hy.magnitude)
  · have h := add_error x y xh yh (xh+yh) Ex Ey 0 hx.error hy.error (by simp)
    simpa using h

theorem ErrorBound.sub (x y xh yh Mx My Ex Ey : Real)
    (hx : ErrorBound x xh Mx Ex) (hy : ErrorBound y yh My Ey) :
    ErrorBound (x-y) (xh-yh) (Mx+My) (Ex+Ey) := by
  constructor
  · exact le_trans (abs_sub x y) (add_le_add hx.magnitude hy.magnitude)
  · have h := sub_error x y xh yh (xh-yh) Ex Ey 0 hx.error hy.error (by simp)
    simpa using h

theorem ErrorBound.mul (x y xh yh Mx My Ex Ey : Real)
    (hx : ErrorBound x xh Mx Ex) (hy : ErrorBound y yh My Ey) :
    ErrorBound (x*y) (xh*yh) (Mx*My) (Mx*Ey+My*Ex+Ex*Ey) := by
  constructor
  · rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_right hx.magnitude (abs_nonneg y))
      (mul_le_mul_of_nonneg_left hy.magnitude (le_trans (abs_nonneg x) hx.magnitude))
  · exact mul_input_error x y xh yh Ex Ey Mx My hx.error hy.error hx.magnitude hy.magnitude

/-- The divisor is the same positive real in the exact and approximate expression.
Any error in forming a stored divisor must be handled separately. -/
theorem ErrorBound.div_const (x xh M E q : Real)
    (hx : ErrorBound x xh M E) (hq : 0 < q) :
    ErrorBound (x/q) (xh/q) (M/q) (E/q) := by
  constructor
  · rw [abs_div, abs_of_pos hq]
    exact div_le_div_of_nonneg_right hx.magnitude (le_of_lt hq)
  · rw [← sub_div, abs_div, abs_of_pos hq]
    exact div_le_div_of_nonneg_right hx.error (le_of_lt hq)

end heat_rounding
