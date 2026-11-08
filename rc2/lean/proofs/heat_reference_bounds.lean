import proofs.heat_reference
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Candidate derivative identities and uniform bounds for the nonconstant
cosine reference. Not certified until compiled with a complete local audit. -/
namespace heat_reference

theorem time_iterated (D k x : Real) (n : Nat) :
    iteratedDeriv n (fun t => profile D k x t) =
      fun t => (-D*k^2)^n * profile D k x t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [deriv_const_mul_field, (time_derivative D k x t).deriv]
    ring

theorem space_iterated_even (D k t : Real) (n : Nat) :
    iteratedDeriv (2*n) (fun x => profile D k x t) =
      fun x => (-k^2)^n * profile D k x t := by
  have hfirst : deriv (fun x => profile D k x t) =
      fun x => spatialDerivative D k x t := by
    funext x
    exact (space_derivative D k x t).deriv
  have hsecond : deriv (fun x => spatialDerivative D k x t) =
      fun x => -k^2 * profile D k x t := by
    funext x
    exact (space_second_derivative D k x t).deriv
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by ring,
      iteratedDeriv_succ, iteratedDeriv_succ, ih,
      deriv_const_mul_field', hfirst, deriv_const_mul_field', hsecond]
    funext x
    ring

/-- Uniform amplitude on nonnegative times; no Gaussian boundary mismatch. -/
theorem profile_abs_le_one (D k x t : Real) (hD : 0 ≤ D) (ht : 0 ≤ t) :
    |profile D k x t| ≤ 1 := by
  have he : Real.exp (-D*k^2*t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hn : 0 ≤ D*k^2*t := mul_nonneg (mul_nonneg hD (sq_nonneg k)) ht
    simpa only [neg_mul] using (neg_nonpos.mpr hn)
  dsimp [profile]
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-D*k^2*t) * |Real.cos (k*x)| ≤ Real.exp (-D*k^2*t)*1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ ≤ 1 := by simpa using he

theorem fourth_spatial_bound (D k x t : Real) (hD : 0 ≤ D) (ht : 0 ≤ t) :
    |iteratedDeriv 4 (fun y => profile D k y t) x| ≤ k^4 := by
  have hid := congrFun (space_iterated_even D k t 2) x
  change iteratedDeriv 4 (fun y => profile D k y t) x = _ at hid
  rw [hid, abs_mul, abs_pow, abs_neg, abs_of_nonneg (sq_nonneg k)]
  calc
    (k^2)^2 * |profile D k x t| ≤ (k^2)^2*1 :=
      mul_le_mul_of_nonneg_left (profile_abs_le_one D k x t hD ht) (sq_nonneg _)
    _ = k^4 := by ring

theorem sixth_spatial_bound (D k x t : Real) (hD : 0 ≤ D) (ht : 0 ≤ t) :
    |iteratedDeriv 6 (fun y => profile D k y t) x| ≤ k^6 := by
  have hid := congrFun (space_iterated_even D k t 3) x
  change iteratedDeriv 6 (fun y => profile D k y t) x = _ at hid
  rw [hid, abs_mul, abs_pow, abs_neg, abs_of_nonneg (sq_nonneg k)]
  calc
    (k^2)^3 * |profile D k x t| ≤ (k^2)^3*1 :=
      mul_le_mul_of_nonneg_left (profile_abs_le_one D k x t hD ht) (by positivity)
    _ = k^6 := by ring

theorem third_time_bound (D k x t : Real) (hD : 0 ≤ D) (ht : 0 ≤ t) :
    |iteratedDeriv 3 (fun s => profile D k x s) t| ≤ D^3*k^6 := by
  rw [time_iterated, abs_mul, abs_pow]
  have hc : |-D*k^2| = D*k^2 := by
    rw [show -D*k^2 = -(D*k^2) by ring, abs_neg,
      abs_of_nonneg (mul_nonneg hD (sq_nonneg k))]
  rw [hc]
  calc
    (D*k^2)^3 * |profile D k x t| ≤ (D*k^2)^3*1 :=
      mul_le_mul_of_nonneg_left (profile_abs_le_one D k x t hD ht) (by positivity)
    _ = D^3*k^6 := by ring

end heat_reference
#print axioms heat_reference.time_iterated
#print axioms heat_reference.space_iterated_even
#print axioms heat_reference.profile_abs_le_one
#print axioms heat_reference.fourth_spatial_bound
#print axioms heat_reference.sixth_spatial_bound
#print axioms heat_reference.third_time_bound
