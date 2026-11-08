import BenchmarkNativeHalf

namespace FluxWitnessNominal
open FluxWitness400 heat_rounding heat_grid_bridge heat_1d.FiniteGrid

/-- Compare the stored and physical exponents before multiplying by π². -/
theorem decay_coeff_gap :
    |storedD * (223 * stepTime) / (400^2 * storedQ) - (1/3600 : ℝ)| ≤
      93 / 10^22 := by
  norm_num [storedD, storedQ, stepTime, abs_of_nonneg, abs_of_nonpos] <;> norm_num

/-- The cell phases agree. The exponents differ by less than 10⁻¹⁹. -/
theorem phase_and_decay (i : Fin 400) :
    waveNumber * cell spacing i = Real.pi * (2 * (i.val : ℝ) + 1) / 800 ∧
    |modelD * waveNumber^2 * (223 * stepTime) - Real.pi^2 / 3600| ≤ 1 / 10^19 := by
  constructor
  · unfold waveNumber cell spacing
    ring
  · have h : modelD * waveNumber^2 * (223 * stepTime) - Real.pi^2 / 3600 =
        Real.pi^2 * (storedD * (223 * stepTime) / (400^2 * storedQ) - 1/3600) := by
      rw [modelD, coefficient_agrees]
      unfold effectiveDiffusivity waveNumber spacing storedQ
      ring
    rw [h, abs_mul, abs_of_nonneg (sq_nonneg Real.pi)]
    have hp : Real.pi ≤ 31416 / 10000 := by linarith [Real.pi_lt_d4]
    have hp2 : Real.pi^2 ≤ (31416/10000 : ℝ)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) (show 0 ≤ 31416/10000 + Real.pi by positivity)]
    calc
      _ ≤ (31416/10000 : ℝ)^2 * (93/10^22) :=
        mul_le_mul hp2 decay_coeff_gap (abs_nonneg _) (sq_nonneg _)
      _ ≤ _ := by norm_num

end FluxWitnessNominal
#print axioms FluxWitnessNominal.phase_and_decay
