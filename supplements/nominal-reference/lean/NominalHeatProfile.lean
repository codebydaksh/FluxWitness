import NominalHeatParameters

namespace FluxWitnessNominal
open FluxWitness400 heat_rounding heat_grid_bridge heat_reference heat_1d.FiniteGrid

private theorem exp_ordered {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x-y| := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (x-y)) (Real.exp_nonneg y)
  rw [← Real.exp_add, sub_add_cancel] at h
  have hy1 : Real.exp y ≤ 1 := by simpa using Real.exp_le_exp.mpr hy
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hy1)]

private theorem exp_contract {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x-y| := by
  rcases le_total x y with h | h
  · exact exp_ordered h hy
  · simpa only [abs_sub_comm (Real.exp y) (Real.exp x), abs_sub_comm y x] using exp_ordered h hx

noncomputable def nominalCell (i : Fin 400) : ℝ :=
  1/2 * Real.exp (-(Real.pi^2/3600)) * Real.cos (Real.pi * (2*(i.val:ℝ)+1)/800) + 1

theorem profile_gap (i : Fin 400) :
    |(1/2 * profile modelD waveNumber (cell spacing i) (223*stepTime) + 1) -
      nominalCell i| ≤ 5/10^20 := by
  let a := modelD * waveNumber^2 * (223*stepTime)
  let b := Real.pi^2/3600
  let c := Real.cos (Real.pi * (2*(i.val:ℝ)+1)/800)
  have hD : 0 ≤ modelD := by
    rw [modelD, coefficient_agrees]
    norm_num [effectiveDiffusivity, storedD, storedQ, spacing]
  have ht : 0 ≤ stepTime := by norm_num [stepTime]
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have he := exp_contract (neg_nonpos.mpr ha) (neg_nonpos.mpr hb)
  have hab : |-a - -b| ≤ 1/10^19 := by
    rw [show -a - -b = -(a-b) by ring, abs_neg]
    exact (phase_and_decay i).2
  have hc : |c| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  unfold profile nominalCell
  rw [(phase_and_decay i).1]
  change |(1/2 * (Real.exp _ * c) + 1) - (1/2 * Real.exp (-b) * c + 1)| ≤ _
  rw [show -modelD * waveNumber^2 * (223*stepTime) = -a by dsimp [a]; ring]
  rw [show (1/2 * (Real.exp (-a)*c)+1) - (1/2 * Real.exp (-b)*c+1) =
      (Real.exp (-a) - Real.exp (-b))*c/2 by ring, abs_div, abs_mul]
  have hprod := mul_le_mul (he.trans hab) hc (abs_nonneg c) (by norm_num : (0:ℝ) ≤ 1/10^19)
  norm_num at hprod ⊢ <;> linarith

end FluxWitnessNominal
#print axioms FluxWitnessNominal.profile_gap
