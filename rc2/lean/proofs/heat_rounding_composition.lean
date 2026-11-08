import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Candidate compositional rounding-error mathematics.
No IEEE implementation is defined or verified here. Local rounding inequalities
are explicit hypotheses, and this file does not yet establish a Heun-step bound.
-/
namespace heat_rounding

theorem compose_error (target intermediate computed e localError : Real)
    (hprior : |intermediate - target| ≤ e)
    (hlocal : |computed - intermediate| ≤ localError) :
    |computed - target| ≤ localError + e := by
  calc
    |computed - target| = |(computed - intermediate) + (intermediate - target)| := by
      congr 1 <;> ring
    _ ≤ |computed - intermediate| + |intermediate - target| := abs_add_le _ _
    _ ≤ localError + e := add_le_add hlocal hprior

theorem add_error (x y xh yh computed ex ey localError : Real)
    (hx : |xh - x| ≤ ex) (hy : |yh - y| ≤ ey)
    (hlocal : |computed - (xh + yh)| ≤ localError) :
    |computed - (x + y)| ≤ localError + (ex + ey) := by
  apply compose_error (x + y) (xh + yh) computed (ex + ey) localError
  · calc
      |xh + yh - (x + y)| = |(xh - x) + (yh - y)| := by congr 1 <;> ring
      _ ≤ |xh - x| + |yh - y| := abs_add_le _ _
      _ ≤ ex + ey := add_le_add hx hy
  · exact hlocal

theorem sub_error (x y xh yh computed ex ey localError : Real)
    (hx : |xh - x| ≤ ex) (hy : |yh - y| ≤ ey)
    (hlocal : |computed - (xh - yh)| ≤ localError) :
    |computed - (x - y)| ≤ localError + (ex + ey) := by
  apply compose_error (x - y) (xh - yh) computed (ex + ey) localError
  · calc
      |xh - yh - (x - y)| = |(xh - x) - (yh - y)| := by congr 1 <;> ring
      _ ≤ |xh - x| + |yh - y| := abs_sub _ _
      _ ≤ ex + ey := add_le_add hx hy
  · exact hlocal

theorem mul_input_error (x y xh yh ex ey Mx My : Real)
    (hx : |xh - x| ≤ ex) (hy : |yh - y| ≤ ey)
    (hMx : |x| ≤ Mx) (hMy : |y| ≤ My) :
    |xh * yh - x * y| ≤ Mx * ey + My * ex + ex * ey := by
  have hex : 0 ≤ ex := le_trans (abs_nonneg _) hx
  have hey : 0 ≤ ey := le_trans (abs_nonneg _) hy
  have h1 : |x * (yh-y)| ≤ Mx * ey := by
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hMx hey)
  have h2 : |y * (xh-x)| ≤ My * ex := by
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
      (mul_le_mul_of_nonneg_right hMy hex)
  have h3 : |(xh-x) * (yh-y)| ≤ ex * ey := by
    rw [abs_mul]
    exact le_trans (mul_le_mul_of_nonneg_right hx (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hy hex)
  calc
    |xh*yh-x*y| = |(x*(yh-y)+y*(xh-x))+(xh-x)*(yh-y)| := by congr 1 <;> ring
    _ ≤ |x*(yh-y)+y*(xh-x)| + |(xh-x)*(yh-y)| := abs_add_le _ _
    _ ≤ (|x*(yh-y)|+|y*(xh-x)|)+|(xh-x)*(yh-y)| :=
      add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ Mx*ey+My*ex+ex*ey := add_le_add (add_le_add h1 h2) h3

theorem rounded_mul_error (x y xh yh computed ex ey Mx My localError : Real)
    (hx : |xh-x| ≤ ex) (hy : |yh-y| ≤ ey)
    (hMx : |x| ≤ Mx) (hMy : |y| ≤ My)
    (hlocal : |computed-xh*yh| ≤ localError) :
    |computed-x*y| ≤ localError + (Mx*ey+My*ex+ex*ey) := by
  exact compose_error (x*y) (xh*yh) computed _ localError
    (mul_input_error x y xh yh ex ey Mx My hx hy hMx hMy) hlocal

/-- Relative-plus-absolute local rounding law, including an additive underflow
allowance. The law is assumed at this input; it is not proved for IEEE here. -/
theorem round_after_error (target input computed e M unit allowance : Real)
    (hu : 0 ≤ unit) (hprior : |input-target| ≤ e) (hM : |target| ≤ M)
    (hround : |computed-input| ≤ unit*|input|+allowance) :
    |computed-target| ≤ e + unit*(M+e)+allowance := by
  have hin : |input| ≤ M+e := by
    have htri := abs_add_le (input-target) target
    have hid : input-target+target = input := by ring
    rw [hid] at htri
    linarith
  have hlocal : |computed-input| ≤ unit * (M + e) + allowance := by
    calc
      |computed-input| ≤ unit * |input| + allowance := hround
      _ ≤ unit * (M + e) + allowance :=
        add_le_add (mul_le_mul_of_nonneg_left hin hu) (le_refl allowance)
  have h := compose_error target input computed e (unit*(M+e)+allowance) hprior hlocal
  linarith

end heat_rounding

