import proofs.heat_final2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.GCongr

/-! n = 400 benchmark instantiation of `heat_final2.harness_error_bound_ranged`.
CANDIDATE, NOT COMPILED. Exact reals only.

The numeric hypotheses are the facts about the STORED binary64 values and the tool-certified premises;
each is checked outside Lean (see verify_n400_constants.py):
  hh0 hh1   h   = fl(6.0/400.0)
  hD0 hD1   D   = D_eff = fl(0.01) * h^2 / fl(h*h)
  hdt0 hdt1 dt  = fl(1.0/223)                                  (N = 223 steps)
  heps0 heps1  eps0 = interval-arithmetic bound on the initial array error  (certify_initial.py)
  hdelta0 hdelta1  delta = per-step rounding bound                         (Gappa, |u| <= 2)
  hperturb  the per-step implementation premise, only while |computed j| <= 2   (Gappa + C model)
Conclusion: the computed array after 223 steps is within 7.05e-9 of the exact reference
  1/2 * exp(-D k^2 t) cos(k y) + 1  at the cell centres y, t = 223*dt. -/
namespace heat_benchmark
open heat_1d.FiniteGrid heat_grid_bridge heat_reference heat_final2

theorem elapsed_const (c : Real) (K : Nat) : elapsed (fun _ => c) K = (K : Real) * c := by
  induction K with
  | zero =>
    have e0 : elapsed (fun _ : Nat => c) 0 = 0 := rfl
    rw [e0]
    simp
  | succ K ih =>
    have e : elapsed (fun _ : Nat => c) (K+1) = elapsed (fun _ : Nat => c) K + c := rfl
    rw [e, ih]
    push_cast
    ring

theorem benchmark_n400
    (D h k dt eps0 δ : Real) (computed : Nat → Fin 400 → Real)
    (hh0 : (149999999999999994 / 10000000000000000000 : Real) ≤ h) (hh1 : h ≤ (3 / 200 : Real))
    (hD0 : 0 ≤ D) (hD1 : D ≤ (100000000000000011 / 10000000000000000000 : Real))
    (hdt0 : 0 ≤ dt) (hdt1 : dt ≤ (44843049327354261 / 10000000000000000000 : Real))
    (hk : k * (((400 : Nat) : Real) * h) = Real.pi)
    (heps0 : 0 ≤ eps0) (heps1 : eps0 ≤ (24854 / 100000000000000000000 : Real))
    (hdelta0 : 0 ≤ δ) (hdelta1 : δ ≤ (27100 / 10000000000000000000 : Real))
    (hinit : ∀ i, |computed 0 i - (1/2 * Real.cos (k * cell h i) + 1)| ≤ eps0)
    (hperturb : ∀ j, j < 223 → (∀ i, |computed j i| ≤ 2) → Bounded (-δ) δ
      (fun i => computed (j+1) i - heun D dt h (computed j) i))
    (i : Fin 400) :
    |computed 223 i - (1/2 * profile D k (cell h i) (((223 : Nat) : Real) * dt) + 1)| ≤
      (705 / 100000000000 : Real) := by
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

#print axioms heat_benchmark.elapsed_const
#print axioms heat_benchmark.benchmark_n400
