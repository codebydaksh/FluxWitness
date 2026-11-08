import proofs.C1StepAgreement

namespace FluxWitnessC2

open heat_rounding heat_1d.FiniteGrid
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat

private def wpLeft (i : Fin 400) : Fin 400 :=
  if h : i.val > 0 then ⟨i.val - 1, by omega⟩ else 0

private def wpRight (i : Fin 400) : Fin 400 :=
  if h : i.val < 399 then ⟨i.val + 1, by omega⟩ else ⟨399, by decide⟩

private theorem wpLeft_eq (i : Fin 400) : wpLeft i = left i := by
  apply Fin.ext
  unfold wpLeft left
  split_ifs <;> simp_all <;> omega

private theorem wpRight_eq (i : Fin 400) : wpRight i = right i := by
  have hi := i.isLt
  apply Fin.ext
  unfold wpRight right
  split_ifs <;> simp_all <;> omega

-- Lean interpretation of the exported expression. Every rounding site uses FloatLib.
private noncomputable def wpEuler (l c r dt : ℝ) : ℝ :=
  let R : ℝ → ℝ := fun x => Model.roundAt binary64 x
  let d : ℝ := 5764607523034235 / 576460752303423488
  let q : ℝ := 4150517416584649 / 18446744073709551616
  let stencil := R (d * R (R (R (r - R (2*c)) + l) / q))
  R (c + R (dt * stencil))

noncomputable def interpretedStep (u : Fin 400 → ℝ) (dt : ℝ) (i : Fin 400) : ℝ :=
  let stage := fun j => wpEuler (u (wpLeft j)) (u j) (u (wpRight j)) dt
  let t := wpEuler (stage (wpLeft i)) (stage i) (stage (wpRight i)) dt
  Model.roundAt binary64 (Model.roundAt binary64 ((1/2 : ℝ) * u i) +
    Model.roundAt binary64 ((1/2 : ℝ) * t))

theorem decoded_step_agrees (v : Fin 400 → Model binary64) (dt : ℝ)
    (hf : ∀ j, Model.isFinite (v j) = true)
    (hu : ∀ j, |Model.toReal (v j)| ≤ 2) (hdt : |dt| ≤ 9/2000) (i : Fin 400) :
    interpretedStep (fun j => Model.toReal (v j)) dt i =
      roundedStep c1Arithmetic storedD dt storedQ (fun j => Model.toReal (v j)) i := by
  rw [boundedStep_eq_explicit_rounded _ _ hu
    (fun j => Model.roundAt_toReal_eq (v j) (hf j)) hdt i]
  have half (x : ℝ) : (1/2 : ℝ) * x = x/2 := by ring
  simp only [interpretedStep, c1ExplicitStep, wpLeft_eq, wpRight_eq, half]
  <;> rfl

end FluxWitnessC2

#print axioms FluxWitnessC2.decoded_step_agrees
