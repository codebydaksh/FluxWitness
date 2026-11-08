/- Conditional on the benchmark input hypotheses. Both arithmetic laws are supplied by FloatLib. Requires a single Lean 4.35 build. -/
import proofs.Binary64Bridge
import FloatLibWorkspace.StoredDiffusivityMinimal
import FloatLibWorkspace.Binary64Half

set_option autoImplicit false

namespace heat_rounding
noncomputable section

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat
open heat_1d.FiniteGrid heat_grid_bridge heat_reference

theorem verified_benchmark_binary64_round_nativeHalf
    (D h k dt eps0 : Real) (u0 : Fin 400 → Real)
    (hD_eq : D = effectiveDiffusivity storedD h storedQ)
    (hh0 : (149999999999999994 / 10000000000000000000 : Real) ≤ h)
    (hh1 : h ≤ (3/200 : Real))
    (hD0 : 0 ≤ D)
    (hD1 : D ≤ (100000000000000011 / 10000000000000000000 : Real))
    (hdt0 : 0 ≤ dt)
    (hdt1 : dt ≤ (44843049327354261 / 10000000000000000000 : Real))
    (hk : k * (((400 : Nat) : Real) * h) = Real.pi)
    (heps0 : 0 ≤ eps0)
    (heps1 : eps0 ≤ (24854 / 100000000000000000000 : Real))
    (hinit : ∀ i, |u0 i - (1/2 * Real.cos (k * cell h i) + 1)| ≤ eps0)
    (i : Fin 400) :
    |roundedEvolution
        (arithmeticFromBoundedLaws 1000000
          (1/9007199254740992) (1/10^30)
          (Model.roundAt binary64) heat_rounding_b64.nativeHalf
          (by norm_num) (by norm_num)
          (fun x hx => heat_rounding_b64.binary64_bounded_round_law x hx)
          (fun x hx => heat_rounding_b64.binary64_half_law x hx))
        (fun _ => dt) u0 223 i -
      (1/2 * profile D k (cell h i) (((223 : Nat) : Real) * dt) + 1)| ≤
        (705 / 100000000000 : Real) := by
  exact verified_benchmark
    (Model.roundAt binary64) heat_rounding_b64.nativeHalf
    (fun x hx => heat_rounding_b64.binary64_bounded_round_law x hx)
    (fun x hx => heat_rounding_b64.binary64_half_law x hx)
    D h k dt eps0 u0 hD_eq hh0 hh1 hD0 hD1 hdt0 hdt1 hk heps0 heps1 hinit i

end
end heat_rounding

#print axioms heat_rounding.verified_benchmark_binary64_round_nativeHalf

namespace FluxWitness400
noncomputable section
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat
open heat_1d.FiniteGrid heat_grid_bridge heat_reference heat_rounding

def spacing : Real := 1080863910568919 / 72057594037927936
def stepTime : Real := 5170051590165233 / 1152921504606846976
def waveNumber : Real := Real.pi / (400 * spacing)
def initialBudget : Real := 24854 / 100000000000000000000
def modelD : Real := effectiveDiffusivity (Model.roundAt binary64 (1/100)) spacing storedQ

theorem coefficient_agrees : Model.roundAt binary64 (1/100) = storedD := by
  calc
    Model.roundAt binary64 (1/100) =
        Model.toReal (FluxWitnessR1.asLib (0.01 : Float)) := Model.stored_diffusivity_A6.symm
    _ = storedD := Model.fw_toReal_D001

private theorem modelD_eq : modelD = effectiveDiffusivity storedD spacing storedQ := by
  rw [modelD, coefficient_agrees]

private theorem phase (i : Fin 400) :
    waveNumber * cell spacing i = Real.pi * (2 * (i.val : Real) + 1) / 800 := by
  unfold waveNumber cell spacing
  ring

-- For this concrete model, the array-specific premise is the initial cosine error.
-- Native instruction semantics and driver control flow do not occur in this statement.
theorem model_benchmark (u0 : Fin 400 → Real)
    (hinit : ∀ i, |u0 i - (1/2 * Real.cos (Real.pi * (2 * (i.val : Real) + 1) / 800) + 1)| ≤ initialBudget)
    (i : Fin 400) :
    |roundedEvolution
      (arithmeticFromBoundedLaws 1000000 (1/9007199254740992) (1/10^30)
        (Model.roundAt binary64) heat_rounding_b64.nativeHalf
        (by norm_num) (by norm_num)
        heat_rounding_b64.binary64_bounded_round_law heat_rounding_b64.binary64_half_law)
      (fun _ => stepTime) u0 223 i -
      (1/2 * profile modelD waveNumber (cell spacing i) (223 * stepTime) + 1)| ≤
      (705 / 100000000000 : Real) := by
  apply verified_benchmark_binary64_round_nativeHalf modelD spacing waveNumber stepTime initialBudget u0
  · exact modelD_eq
  · norm_num [spacing]
  · norm_num [spacing]
  · rw [modelD_eq]
    norm_num [effectiveDiffusivity, storedD, storedQ, spacing]
  · rw [modelD_eq]
    norm_num [effectiveDiffusivity, storedD, storedQ, spacing]
  · norm_num [stepTime]
  · norm_num [stepTime]
  · unfold waveNumber spacing
    ring
  · norm_num [initialBudget]
  · norm_num [initialBudget]
  · intro j
    rw [phase]
    exact hinit j

end
end FluxWitness400
#print axioms FluxWitness400.coefficient_agrees
#print axioms FluxWitness400.model_benchmark
