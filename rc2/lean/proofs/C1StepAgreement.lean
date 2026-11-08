import proofs.C1StageBounds

namespace heat_rounding
noncomputable section
open heat_1d.FiniteGrid
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat

-- Explicit rounded operation tree, not a definition of C execution.
def c1ExplicitStep {n : Nat} (u : Fin n → Real) (dt : Real) (i : Fin n) : Real :=
  let s := fun j => c1ExplicitRoundedEuler (u (left j)) (u j) (u (right j)) dt
  let t := c1ExplicitRoundedEuler (s (left i)) (s i) (s (right i)) dt
  Model.roundAt binary64 (Model.roundAt binary64 (u i/2) + Model.roundAt binary64 (t/2))

theorem boundedStep_eq_explicit_rounded {n : Nat} (u : Fin n → Real) (dt : Real)
    (hu : ∀ j, |u j| ≤ 2)
    (hrep : ∀ j, Model.roundAt binary64 (u j) = u j)
    (hdt : |dt| ≤ 9/2000) (i : Fin n) :
    roundedStep c1Arithmetic storedD dt storedQ u i = c1ExplicitStep u dt i := by
  let s := fun j => roundedEuler c1Arithmetic (u (left j)) (u j) (u (right j)) dt storedD storedQ
  let e := fun j => c1ExplicitRoundedEuler (u (left j)) (u j) (u (right j)) dt
  have hu4 : ∀ j, |u j| ≤ 4 := fun j => le_trans (hu j) (by norm_num)
  have hse : ∀ j, s j = e j := by
    intro j
    exact boundedEuler_eq_explicit_rounded _ _ _ _ (hu4 (left j)) (hu4 j)
      (hu4 (right j)) hdt (hrep j)
  have hs : ∀ j, |s j| ≤ 4 := by
    intro j
    exact c1_first_stage_bound _ _ _ _ (hu (left j)) (hu j) (hu (right j)) hdt
  have hsRep : ∀ j, Model.roundAt binary64 (s j) = s j := by
    intro j
    exact c1_euler_grid_representable _ _ _ _ (hu4 (left j)) (hu4 j) (hu4 (right j)) hdt
  let t := roundedEuler c1Arithmetic (s (left i)) (s i) (s (right i)) dt storedD storedQ
  have huUnit : c1Arithmetic.unit ≤ 1 := by norm_num [c1Arithmetic, arithmeticFromBoundedLaws]
  have heAllowance : c1Arithmetic.allowance ≤ 1 := by norm_num [c1Arithmetic, arithmeticFromBoundedLaws]
  have ht : |t| ≤ 487 :=
    (storedEuler_operand_domain c1Arithmetic huUnit heAllowance _ _ _ _
      (hs (left i)) (hs i) (hs (right i)) hdt).2
  have htRep : Model.roundAt binary64 t = t :=
    c1_euler_grid_representable _ _ _ _ (hs (left i)) (hs i) (hs (right i)) hdt
  have hte : t = c1ExplicitRoundedEuler (s (left i)) (s i) (s (right i)) dt :=
    boundedEuler_eq_explicit_rounded _ _ _ _ (hs (left i)) (hs i) (hs (right i)) hdt (hsRep i)
  have htEq : t = c1ExplicitRoundedEuler (e (left i)) (e i) (e (right i)) dt := by
    rw [hte, hse (left i), hse i, hse (right i)]
  change c1Arithmetic.round (c1Arithmetic.half (u i) + c1Arithmetic.half t) = _
  rw [boundedHalfSum_eq_explicit_rounded (u i) t (hu i) ht (hrep i) htRep]
  change Model.roundAt binary64 (Model.roundAt binary64 (u i/2) + Model.roundAt binary64 (t/2)) =
    Model.roundAt binary64 (Model.roundAt binary64 (u i/2) +
      Model.roundAt binary64 (c1ExplicitRoundedEuler (e (left i)) (e i) (e (right i)) dt/2))
  rw [htEq]

end
end heat_rounding
