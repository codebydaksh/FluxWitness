import WiderInitial
import NominalHeatProfile
set_option autoImplicit false

namespace heat_benchmark
open heat_1d.FiniteGrid heat_grid_bridge heat_reference heat_final2

theorem benchmark_n400_tight
    (D h k dt eps0 δ : Real) (computed : Nat → Fin 400 → Real)
    (hh0 : (149999999999999994 / 10000000000000000000 : Real) ≤ h) (hh1 : h ≤ (3 / 200 : Real))
    (hD0 : 0 ≤ D) (hD1 : D ≤ (100000000000000011 / 10000000000000000000 : Real))
    (hdt0 : 0 ≤ dt) (hdt1 : dt ≤ (44843049327354261 / 10000000000000000000 : Real))
    (hk : k * (((400 : Nat) : Real) * h) = Real.pi)
    (heps0 : 0 ≤ eps0) (heps1 : eps0 ≤ (1 / 1000000000000000 : Real))
    (hdelta0 : 0 ≤ δ) (hdelta1 : δ ≤ (27100 / 10000000000000000000 : Real))
    (hinit : ∀ i, |computed 0 i - (1/2 * Real.cos (k * cell h i) + 1)| ≤ eps0)
    (hperturb : ∀ j, j < 223 → (∀ i, |computed j i| ≤ 2) → Bounded (-δ) δ
      (fun i => computed (j+1) i - heun D dt h (computed j) i))
    (i : Fin 400) :
    |computed 223 i - (1/2 * profile D k (cell h i) (((223 : Nat) : Real) * dt) + 1)| ≤
      (7049 / 1000000000000 : Real) := by
  have hlo_pos : (0 : Real) < (149999999999999994 / 10000000000000000000 : Real) := by norm_num
  have hh : 0 < h := lt_of_lt_of_le hlo_pos hh0
  have hpi : Real.pi < (31416 / 10000 : Real) := by
    first
      | (have h4 := Real.pi_lt_d4; linarith)
      | (have h4 := Real.pi_lt_d4; norm_num at h4 ⊢; linarith)
      | (have h6 := Real.pi_lt_d6; norm_num at h6 ⊢; linarith)
  have h400 : (59999 / 10000 : Real) ≤ ((400 : Nat) : Real) * h := by
    have hc : ((59999 / 10000 : Real)) ≤ 400 * (149999999999999994 / 10000000000000000000 : Real) := by norm_num
    push_cast
    linarith
  have hk0 : 0 ≤ k := by
    by_contra hneg
    replace hneg : k < 0 := not_le.mp hneg
    have hX : (0 : Real) < ((400 : Nat) : Real) * h := by positivity
    have hm := mul_neg_of_neg_of_pos hneg hX
    linarith [Real.pi_pos]
  have hk1 : k ≤ (52361 / 100000 : Real) := by
    by_contra hcon
    have hlt : (52361 / 100000 : Real) < k := not_le.mp hcon
    have hmul1 : (52361 / 100000 : Real) * (59999 / 10000 : Real) < k * (59999 / 10000 : Real) :=
      mul_lt_mul_of_pos_right hlt (by norm_num)
    have hmul3 : k * (59999 / 10000 : Real) ≤ k * (((400 : Nat) : Real) * h) :=
      mul_le_mul_of_nonneg_left h400 hk0
    have hmul2 := lt_of_lt_of_le hmul1 hmul3
    rw [hk] at hmul2
    have hnum : (31416 / 10000 : Real) < (52361 / 100000 : Real) * (59999 / 10000 : Real) := by
      norm_num
    linarith [hpi, hnum, hmul2]
  have hCFL : ∀ j : Nat, 2*D*((fun _ : Nat => dt) j) ≤ h*h := by
    intro j
    show 2*D*dt ≤ h*h
    calc 2*D*dt ≤ 2*(100000000000000011 / 10000000000000000000 : Real)*(44843049327354261 / 10000000000000000000 : Real) := by gcongr
      _ ≤ (149999999999999994 / 10000000000000000000 : Real)*(149999999999999994 / 10000000000000000000 : Real) := by norm_num
      _ ≤ h*h := by gcongr
  have hST : (D*h^2*k^4/12 + (D^2*h^2*k^6/12)*dt + (D^3*k^6/6)*dt^2) * (223 * dt) ≤ (14095 / 1000000000000 : Real) := by
    calc (D*h^2*k^4/12 + (D^2*h^2*k^6/12)*dt + (D^3*k^6/6)*dt^2) * (223 * dt)
        ≤ ((100000000000000011 / 10000000000000000000 : Real)*(3 / 200 : Real)^2*(52361 / 100000 : Real)^4/12
            + ((100000000000000011 / 10000000000000000000 : Real)^2*(3 / 200 : Real)^2*(52361 / 100000 : Real)^6/12)*(44843049327354261 / 10000000000000000000 : Real)
            + ((100000000000000011 / 10000000000000000000 : Real)^3*(52361 / 100000 : Real)^6/6)*(44843049327354261 / 10000000000000000000 : Real)^2) * (223 * (44843049327354261 / 10000000000000000000 : Real)) := by gcongr
      _ ≤ (14095 / 1000000000000 : Real) := by norm_num
  have hT : elapsed (fun _ : Nat => dt) 223 ≤ 223 * dt := by
    rw [elapsed_const]
    norm_num
  have hM : |(1/2 : Real)| + |(1 : Real)| +
      (eps0 + |(1/2 : Real)| * ((D*h^2*k^4/12 + (D^2*h^2*k^6/12)*dt + (D^3*k^6/6)*dt^2) * (223 * dt))
        + ((223 : Nat) : Real) * δ) ≤ 2 := by
    have h1 : |(1/2 : Real)| = 1/2 := abs_of_pos (by norm_num)
    have c : ((223 : Nat) : Real) = 223 := by norm_num
    rw [h1, abs_one, c]
    linarith [hST, heps1, hdelta1]
  have key := harness_error_bound_ranged D h k (1/2) 1 eps0 dt (223 * dt) δ 2
    (fun _ : Nat => dt) computed hh hD0 hk (by norm_num) hdt0 (fun _ => hdt0) (fun _ => le_rfl)
    hCFL hinit 223 hperturb hT hdelta0 heps0 hM i
  rw [elapsed_const] at key
  refine le_trans key ?_
  have h1 : |(1/2 : Real)| = 1/2 := abs_of_pos (by norm_num)
  have c : ((223 : Nat) : Real) = 223 := by norm_num
  rw [h1, c]
  linarith [hST, heps1, hdelta1]


end heat_benchmark

namespace heat_rounding
open heat_1d.FiniteGrid heat_grid_bridge heat_reference

theorem abstract_rounded_benchmark_tight
    (a : LocalArithmetic)
    (ha : a.unit = 1/9007199254740992) (he : a.allowance = 1/10^30)
    (D h k dt eps0 : Real) (u0 : Fin 400 → Real)
    (hD_eq : D = effectiveDiffusivity storedD h storedQ)
    (hh0 : (149999999999999994 / 10000000000000000000 : Real) ≤ h)
    (hh1 : h ≤ (3/200 : Real))
    (hD0 : 0 ≤ D)
    (hD1 : D ≤ (100000000000000011 / 10000000000000000000 : Real))
    (hdt0 : 0 ≤ dt)
    (hdt1 : dt ≤ (44843049327354261 / 10000000000000000000 : Real))
    (hk : k * (((400 : Nat) : Real)*h) = Real.pi)
    (heps0 : 0 ≤ eps0)
    (heps1 : eps0 ≤ (1 / 1000000000000000 : Real))
    (hinit : ∀ i, |u0 i - (1/2 * Real.cos (k*cell h i)+1)| ≤ eps0)
    (i : Fin 400) :
    |roundedEvolution a (fun _ => dt) u0 223 i -
      (1/2 * profile D k (cell h i) (((223 : Nat) : Real)*dt)+1)| ≤
      (7049 / 1000000000000 : Real) := by
  have hh : h ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hh0)
  have hcap : |dt| ≤ (9/2000 : Real) := by
    rw [abs_of_nonneg hdt0]
    linarith
  apply heat_benchmark.benchmark_n400_tight D h k dt eps0 roundingDelta
    (roundedEvolution a (fun _ => dt) u0)
    hh0 hh1 hD0 hD1 hdt0 hdt1 hk heps0 heps1
    (by norm_num [roundingDelta]) (by norm_num [roundingDelta])
    (by simpa only [roundedEvolution] using hinit) ?_ i
  intro j _ hr
  have hr' : Bounded (-2) 2 (roundedEvolution a (fun _ => dt) u0 j) :=
    fun i => abs_le.mp (hr i)
  have hb := roundedStep_perturbation a ha he
    (roundedEvolution a (fun _ => dt) u0 j) hr' dt hcap h hh
  rw [← hD_eq] at hb
  exact hb

end heat_rounding

namespace heat_rounding
noncomputable section

open heat_1d.FiniteGrid heat_grid_bridge heat_reference

theorem verified_benchmark_tight
    (round half : Real -> Real)
    (hr : forall x, |x| <= 1000000 -> |round x - x| <= (1/9007199254740992) * |x| + (1/10^30))
    (hh : forall x, |x| <= 1000000 -> |half x - x/2| <= (1/10^30))
    (D h k dt eps0 : Real) (u0 : Fin 400 -> Real)
    (hD_eq : D = effectiveDiffusivity storedD h storedQ)
    (hh0 : (149999999999999994 / 10000000000000000000 : Real) <= h)
    (hh1 : h <= (3/200 : Real))
    (hD0 : 0 <= D)
    (hD1 : D <= (100000000000000011 / 10000000000000000000 : Real))
    (hdt0 : 0 <= dt)
    (hdt1 : dt <= (44843049327354261 / 10000000000000000000 : Real))
    (hk : k * (((400 : Nat) : Real)*h) = Real.pi)
    (heps0 : 0 <= eps0)
    (heps1 : eps0 <= (1 / 1000000000000000 : Real))
    (hinit : forall i, |u0 i - (1/2 * Real.cos (k*cell h i)+1)| <= eps0)
    (i : Fin 400) :
    |roundedEvolution (arithmeticFromBoundedLaws 1000000 (1/9007199254740992) (1/10^30) round half (by norm_num) (by norm_num) hr hh) (fun _ => dt) u0 223 i -
      (1/2 * profile D k (cell h i) (((223 : Nat) : Real)*dt)+1)| <=
      (7049 / 1000000000000 : Real) := by
  
  let a := arithmeticFromBoundedLaws 1000000 (1/9007199254740992) (1/10^30) round half (by norm_num) (by norm_num) hr hh
  
  -- Using rfl instead of simp to avoid structure projection issues
  apply abstract_rounded_benchmark_tight a (by rfl) (by rfl) D h k dt eps0 u0 hD_eq hh0 hh1 hD0 hD1 hdt0 hdt1 hk heps0 heps1 hinit i

end
end heat_rounding


namespace heat_rounding
noncomputable section

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat
open heat_1d.FiniteGrid heat_grid_bridge heat_reference

theorem verified_benchmark_binary64_round_nativeHalf_tight
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
    (heps1 : eps0 ≤ (1 / 1000000000000000 : Real))
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
        (7049 / 1000000000000 : Real) := by
  exact verified_benchmark_tight
    (Model.roundAt binary64) heat_rounding_b64.nativeHalf
    (fun x hx => heat_rounding_b64.binary64_bounded_round_law x hx)
    (fun x hx => heat_rounding_b64.binary64_half_law x hx)
    D h k dt eps0 u0 hD_eq hh0 hh1 hD0 hD1 hdt0 hdt1 hk heps0 heps1 hinit i

end
end heat_rounding


namespace FluxWitness400
noncomputable section
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat
open heat_1d.FiniteGrid heat_grid_bridge heat_reference heat_rounding




private theorem modelD_eq_tight : modelD = effectiveDiffusivity storedD spacing storedQ := by
  rw [modelD, coefficient_agrees]

private theorem phase_tight (i : Fin 400) :
    waveNumber * cell spacing i = Real.pi * (2 * (i.val : Real) + 1) / 800 := by
  unfold waveNumber cell spacing
  ring

-- For this concrete model, the array-specific premise is the initial cosine error.
-- Native instruction semantics and driver control flow do not occur in this statement.
theorem model_benchmark_tight (u0 : Fin 400 → Real)
    (hinit : ∀ i, |u0 i - (1/2 * Real.cos (Real.pi * (2 * (i.val : Real) + 1) / 800) + 1)| ≤ initialBudgetWide)
    (i : Fin 400) :
    |roundedEvolution
      (arithmeticFromBoundedLaws 1000000 (1/9007199254740992) (1/10^30)
        (Model.roundAt binary64) heat_rounding_b64.nativeHalf
        (by norm_num) (by norm_num)
        heat_rounding_b64.binary64_bounded_round_law heat_rounding_b64.binary64_half_law)
      (fun _ => stepTime) u0 223 i -
      (1/2 * profile modelD waveNumber (cell spacing i) (223 * stepTime) + 1)| ≤
      (7049 / 1000000000000 : Real) := by
  apply verified_benchmark_binary64_round_nativeHalf_tight modelD spacing waveNumber stepTime initialBudgetWide u0
  · exact modelD_eq_tight
  · norm_num [spacing]
  · norm_num [spacing]
  · rw [modelD_eq_tight]
    norm_num [effectiveDiffusivity, storedD, storedQ, spacing]
  · rw [modelD_eq_tight]
    norm_num [effectiveDiffusivity, storedD, storedQ, spacing]
  · norm_num [stepTime]
  · norm_num [stepTime]
  · unfold waveNumber spacing
    ring
  · norm_num [initialBudgetWide]
  · norm_num [initialBudgetWide]
  · intro j
    rw [phase_tight]
    exact hinit j

theorem nominal_benchmark (u0 : Fin 400 → Real)
    (hinit : ∀ i, |u0 i - (1/2 * Real.cos (Real.pi * (2 * (i.val : Real) + 1) / 800) + 1)| ≤ initialBudgetWide)
    (i : Fin 400) :
    |roundedEvolution
      (arithmeticFromBoundedLaws 1000000 (1/9007199254740992) (1/10^30)
        (Model.roundAt binary64) heat_rounding_b64.nativeHalf
        (by norm_num) (by norm_num)
        heat_rounding_b64.binary64_bounded_round_law heat_rounding_b64.binary64_half_law)
      (fun _ => stepTime) u0 223 i -
      FluxWitnessNominal.nominalCell i| ≤
      (705 / 100000000000 : Real) := by
  have hsum := add_le_add (model_benchmark_tight u0 hinit i) (FluxWitnessNominal.profile_gap i)
  exact (abs_sub_le _ (1/2 * profile modelD waveNumber (cell spacing i) (223 * stepTime) + 1)
    (FluxWitnessNominal.nominalCell i)).trans (hsum.trans (by norm_num))

end
end FluxWitness400

#print axioms FluxWitness400.nominal_benchmark
