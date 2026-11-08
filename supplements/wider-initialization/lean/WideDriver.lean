import C3DriverLoop
import WiderInitial
namespace FluxWitnessC3
open heat_rounding heat_1d.FiniteGrid heat_grid_bridge heat_reference FluxWitness400
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat

theorem driver223_of_wp_wide {S : Type} (start : S) (call : S → Option S)
    (live : S → Prop) (cells : S → Fin 400 → Model binary64)
    (wpValue : S → Fin 400 → ℝ)
    (allocator_and_entry_layout : live start)
    (initial_finite : ∀ i, Model.isFinite (cells start i) = true)
    (initial_cosine : ∀ i, |Model.toReal (cells start i) -
      (1/2 * Real.cos (Real.pi * (2 * (i.val : ℝ) + 1) / 800) + 1)| ≤ initialBudgetWide)
    (wp_call : ∀ s, live s → (∀ i, Model.isFinite (cells s i) = true) →
      (∀ i, |Model.toReal (cells s i)| ≤ 2) →
      ∃ t, call s = some t ∧ (∀ i, Model.isFinite (cells t i) = true) ∧
        ∀ i, Model.toReal (cells t i) = wpValue s i)
    (layout_survives : ∀ s t, live s → call s = some t → live t)
    (wp_interpretation : ∀ s, live s → (∀ i, Model.isFinite (cells s i) = true) →
      (∀ i, |Model.toReal (cells s i)| ≤ 2) → ∀ i,
      wpValue s i = FluxWitnessC2.interpretedStep (fun j => Model.toReal (cells s j)) stepTime i) :
    ∃ t, calls call start 223 = some t ∧ live t ∧
      ∀ i, |Model.toReal (cells t i) -
        (1/2 * profile modelD waveNumber (cell spacing i) (223 * stepTime) + 1)| ≤
          705 / 100000000000 := by
  let u0 : Grid := fun i => Model.toReal (cells start i)
  let evolution := roundedEvolution c1Arithmetic (fun _ => stepTime) u0
  have initRange : Bounded (-(151/100)) (151/100) u0 := by
    intro i
    have hi := abs_le.mp (initial_cosine i)
    unfold initialBudgetWide at hi
    change -(151/100) ≤ Model.toReal (cells start i) ∧ Model.toReal (cells start i) ≤ 151/100
    constructor <;> linarith only [Real.neg_one_le_cos (Real.pi * (2 * (i.val : ℝ) + 1) / 800),
      Real.cos_le_one (Real.pi * (2 * (i.val : ℝ) + 1) / 800), hi.1, hi.2]
  have cap : |stepTime| ≤ 9/2000 := by norm_num [stepTime]
  have modelRange (j : Nat) (hj : j ≤ 223) : Bounded (-2) 2 (evolution j) :=
    (roundedEvolution_error_and_range c1Arithmetic rfl rfl spacing (151/100)
      (by norm_num [spacing]) (fun _ => stepTime) u0 223
      (fun _ => by norm_num [stepTime]) (fun _ => cap)
      (fun _ => by norm_num [effectiveDiffusivity, storedD, spacing, storedQ, stepTime])
      initRange (by norm_num [roundingDelta]) j hj).2
  have reachablePrefix (j : Nat) (hj : j ≤ 223) : ∃ s, calls call start j = some s ∧
      live s ∧ (∀ i, Model.isFinite (cells s i) = true) ∧
        ∀ i, Model.toReal (cells s i) = evolution j i := by
    induction j with
    | zero => exact ⟨start, rfl, allocator_and_entry_layout, initial_finite, fun _ => rfl⟩
    | succ j ih =>
      have hj' : j ≤ 223 := by omega
      obtain ⟨s, reached, hl, hf, heq⟩ := ih hj'
      have hb (i : Fin 400) : |Model.toReal (cells s i)| ≤ 2 := by
        rw [heq i]
        exact abs_le.mpr (modelRange j hj' i)
      obtain ⟨t, hs, ht, hout⟩ := wp_call s hl hf hb
      refine ⟨t, ?_, layout_survives s t hl hs, ht, ?_⟩
      · simpa [calls, reached] using hs
      · intro i
        rw [hout i, wp_interpretation s hl hf hb i,
          FluxWitnessC2.decoded_step_agrees (cells s) stepTime hf hb cap i]
        have hgrid : (fun k => Model.toReal (cells s k)) = evolution j := funext heq
        rw [hgrid] <;> rfl
  obtain ⟨t, reached, hl, _, heq⟩ := reachablePrefix 223 (by decide)
  refine ⟨t, reached, hl, fun i => ?_⟩
  rw [heq i]
  exact model_benchmark_wide u0 initial_cosine i

end FluxWitnessC3
#print axioms FluxWitnessC3.driver223_of_wp_wide
