import C3DriverLoop

/-!
Assumption Hunter B001: Lean transcription of the ACSL/WP expression in
rc2/evidence/wp-reference-interpretation-08zrp8uz/probe.c.

This proves equality of two Lean expressions; it does not formalize Frama-C/WP
semantics, C state correspondence, or compiled-binary behavior.
-/

namespace AssumptionHunterBridge

open heat_rounding heat_1d.FiniteGrid heat_grid_bridge heat_reference FluxWitness400
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat

-- Clamped neighbors in the ACSL c5_l/c5_r expression.
private def wpLeft (i : Fin 400) : Fin 400 :=
  if h : i.val > 0 then ⟨i.val - 1, by omega⟩ else 0

private def wpRight (i : Fin 400) : Fin 400 :=
  if h : i.val < 399 then ⟨i.val + 1, by omega⟩ else ⟨399, by decide⟩

-- ACSL c5_e, interpreting every \round_double(\NearestEven,...) as
-- FloatLib's Model.roundAt binary64; this mapping is a trust condition.
private noncomputable def wpEuler (l c r dt : ℝ) : ℝ :=
  let R : ℝ → ℝ := fun x => Model.roundAt binary64 x
  let d : ℝ := 5764607523034235 / 576460752303423488
  let q : ℝ := 4150517416584649 / 18446744073709551616
  let stencil := R (d * R (R (R (r - R (2*c)) + l) / q))
  R (c + R (dt * stencil))

-- ACSL c5_update, with c5_u(k,j) supplied as the grid u.
noncomputable def wpUpdate (u : Fin 400 → ℝ) (dt : ℝ) (i : Fin 400) : ℝ :=
  let stage := fun j => wpEuler (u (wpLeft j)) (u j) (u (wpRight j)) dt
  let t := wpEuler (stage (wpLeft i)) (stage i) (stage (wpRight i)) dt
  Model.roundAt binary64 (Model.roundAt binary64 ((1/2 : ℝ) * u i) +
    Model.roundAt binary64 ((1/2 : ℝ) * t))

theorem wpUpdate_eq_interpretedStep (u : Fin 400 → ℝ) (dt : ℝ) (i : Fin 400) :
    wpUpdate u dt i = FluxWitnessC2.interpretedStep u dt i := by
  rfl

-- Fix the C3 successor to a specific expression and derive its final bound.
-- wp_call_explicit is a STILL-UNPROVED C/WP-to-Lean state correspondence.
theorem driver223_of_explicit_wp
    {S : Type} (start : S) (call : S → Option S)
    (live : S → Prop) (cells : S → Fin 400 → Model binary64)
    (allocator_and_entry_layout : live start)
    (initial_finite : ∀ i, Model.isFinite (cells start i) = true)
    (initial_cosine : ∀ i, |Model.toReal (cells start i) -
      (1/2 * Real.cos (Real.pi * (2 * (i.val : ℝ) + 1) / 800) + 1)| ≤ initialBudget)
    (wp_call_explicit : ∀ s, live s → (∀ i, Model.isFinite (cells s i) = true) →
      (∀ i, |Model.toReal (cells s i)| ≤ 2) →
      ∃ t, call s = some t ∧ (∀ i, Model.isFinite (cells t i) = true) ∧
        ∀ i, Model.toReal (cells t i) =
          wpUpdate (fun j => Model.toReal (cells s j)) stepTime i)
    (layout_survives : ∀ s t, live s → call s = some t → live t) :
    ∃ t, FluxWitnessC3.calls call start 223 = some t ∧ live t ∧
      ∀ i, |Model.toReal (cells t i) -
        (1/2 * profile modelD waveNumber (cell spacing i) (223 * stepTime) + 1)| ≤
          705 / 100000000000 := by
  exact FluxWitnessC3.driver223_of_wp start call live cells
    (fun s i => wpUpdate (fun j => Model.toReal (cells s j)) stepTime i)
    allocator_and_entry_layout initial_finite initial_cosine
    wp_call_explicit layout_survives
    (by
      intro s _ _ _ i
      exact wpUpdate_eq_interpretedStep _ _ _)

end AssumptionHunterBridge

#print axioms AssumptionHunterBridge.wpUpdate_eq_interpretedStep
#print axioms AssumptionHunterBridge.driver223_of_explicit_wp
