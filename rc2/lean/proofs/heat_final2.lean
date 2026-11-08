import proofs.heat_final

/-! Closes the range circularity of heat_final.harness_error_bound.

CANDIDATE, NOT COMPILED. Everything below `harness_error_bound_of_pert` is new; that theorem reuses the
proof body of the accepted `heat_final.harness_error_bound` unchanged, with the perturbation bound taken
as a hypothesis `hpert`.

Result: `harness_error_bound_ranged` needs the per-step implementation premise only while the computed
array stays in [-M, M], and derives that range itself by induction. The remaining C-side premise is
`hperturb` (Gappa/CBMC side), which is NOT proved here. -/
namespace heat_final2
open heat_1d.FiniteGrid heat_grid_bridge heat_reference heat_cosine_conditions heat_final

/-- Prefix version of `perturbed_error_budget`: premises only for steps k < K. -/
theorem perturbed_error_budget_prefix {n : Nat} (D dx initial : Real)
    (dt defect perturbation : Nat → Real)
    (computed reference : Nat → Fin n → Real) (K : Nat)
    (hdx : 0 < dx) (hD : 0 ≤ D)
    (hdt : ∀ k, 0 ≤ dt k) (hCFL : ∀ k, 2*D*dt k ≤ dx*dx)
    (hinit : Bounded (-initial) initial (fun i => computed 0 i-reference 0 i))
    (hdefect : ∀ k, k < K → Bounded (-(defect k)) (defect k)
      (fun i => heun D (dt k) dx (reference k) i-reference (k+1) i))
    (hperturb : ∀ k, k < K → Bounded (-(perturbation k)) (perturbation k)
      (fun i => computed (k+1) i-heun D (dt k) dx (computed k) i))
    (k : Nat) :
    k ≤ K → Bounded (-(errorBudget initial (fun j => defect j+perturbation j) k))
      (errorBudget initial (fun j => defect j+perturbation j) k)
      (fun i => computed k i-reference k i) := by
  induction k with
  | zero => intro _; exact hinit
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    have hstep := heun_difference_bounded D (dt k) dx
      (errorBudget initial (fun j => defect j+perturbation j) k)
      (computed k) (reference k) hdx hD (hdt k) (hCFL k) ih'
    intro i
    obtain ⟨hlo, hhi⟩ := hstep i
    obtain ⟨dlo, dhi⟩ := hdefect k (by omega) i
    obtain ⟨plo, phi⟩ := hperturb k (by omega) i
    simp only [errorBudget]
    constructor <;> linarith

theorem perturbation_only_prefix {n : Nat} (D h δ : Real) (dt : Nat → Real)
    (computed : Nat → Fin n → Real) (K : Nat)
    (hh : 0 < h) (hD : 0 ≤ D) (ht : ∀ k, 0 ≤ dt k) (hCFL : ∀ k, 2*D*dt k ≤ h*h)
    (hperturb : ∀ k, k < K → Bounded (-δ) δ
      (fun i => computed (k+1) i - heun D (dt k) h (computed k) i))
    (i : Fin n) :
    |computed K i - evolve D h dt (computed 0) K i| ≤ (K : Real) * δ := by
  have H := perturbed_error_budget_prefix D h 0 dt (fun _ => 0) (fun _ => δ) computed
    (fun k => evolve D h dt (computed 0) k) K hh hD ht hCFL
    (by intro j; simp [evolve])
    (by intro k _ j; simp [evolve])
    hperturb K le_rfl
  calc |computed K i - evolve D h dt (computed 0) K i|
      ≤ errorBudget 0 (fun _ => (0:Real) + δ) K := abs_le.mpr (H i)
    _ = (K : Real) * δ := budget_const δ K

theorem elapsed_le_of_le (dt : Nat → Real) (ht : ∀ j, 0 ≤ dt j) {j K : Nat} (hjK : j ≤ K) :
    elapsed dt j ≤ elapsed dt K := by
  induction K with
  | zero =>
    have h0 : j = 0 := by omega
    subst h0
    exact le_rfl
  | succ K ih =>
    rcases Nat.lt_or_ge j (K+1) with hlt | hge
    · have hle : j ≤ K := by omega
      have h1 := ih hle
      have e : elapsed dt (K+1) = elapsed dt K + dt K := rfl
      rw [e]
      linarith [ht K]
    · have h0 : j = K+1 := by omega
      subst h0
      exact le_rfl

theorem elapsed_nonneg (dt : Nat → Real) (ht : ∀ j, 0 ≤ dt j) (K : Nat) : 0 ≤ elapsed dt K := by
  have h1 := elapsed_le_of_le dt ht (Nat.zero_le K)
  have e0 : elapsed dt 0 = 0 := rfl
  linarith [h1, e0]

theorem profile_abs_le_one' (D k x t : Real) (hD : 0 ≤ D) (ht : 0 ≤ t) :
    |profile D k x t| ≤ 1 := by
  unfold profile
  rw [abs_mul]
  have hnn : 0 ≤ D * k^2 * t := by positivity
  have hneg : -D * k^2 * t ≤ 0 := by nlinarith [hnn]
  have h1 : |Real.exp (-D * k^2 * t)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    first | exact Real.exp_le_one_iff.mpr hneg | (have h0 := Real.exp_le_exp.mpr hneg; simpa using h0)
  have h2 : |Real.cos (k*x)| ≤ 1 := Real.abs_cos_le_one _
  calc |Real.exp (-D * k^2 * t)| * |Real.cos (k*x)| ≤ 1 * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = 1 := by norm_num

/-- `heat_final.harness_error_bound` with the perturbation bound as a hypothesis (same proof body). -/
theorem harness_error_bound_of_pert {n : Nat} (D h k a b eps0 cap T δ : Real) (dt : Nat → Real)
    (computed : Nat → Fin n → Real)
    (hh : 0 < h) (hD : 0 ≤ D) (hk : k*((n : Real)*h) = Real.pi) (ha : a ≠ 0)
    (hcap0 : 0 ≤ cap) (ht : ∀ j, 0 ≤ dt j) (hcap : ∀ j, dt j ≤ cap)
    (hCFL : ∀ j, 2*D*dt j ≤ h*h)
    (hinit : ∀ i, |computed 0 i - (a*Real.cos (k*cell h i)+b)| ≤ eps0)
    (K : Nat) (i : Fin n)
    (hpert : |computed K i - evolve D h dt (computed 0) K i| ≤ (K : Real) * δ)
    (hT : elapsed dt K ≤ T) :
    |computed K i - (a*profile D k (cell h i) (elapsed dt K)+b)| ≤
      eps0 + |a| * ((D*h^2*k^4/12 + (D^2*h^2*k^6/12)*cap + (D^3*k^6/6)*cap^2)*T)
        + (K : Real)*δ := by
  obtain ⟨w0, hw0⟩ : ∃ w0 : Fin n → Real, w0 = fun j => (computed 0 j - b)/a := ⟨_, rfl⟩
  have hw : ∀ j, w0 j = (computed 0 j - b)/a := by
    intro j
    rw [hw0]
  have habs : |a| ≠ 0 := abs_ne_zero.mpr ha
  -- computed 0 is the affine image of the unit-cosine data w0
  have hcomp0 : computed 0 = fun j => a*w0 j + b := by
    funext j
    show computed 0 j = a * w0 j + b
    rw [hw j]
    have h1 : a * ((computed 0 j - b)/a) = computed 0 j - b := by
      first | (field_simp; ring) | field_simp
    linarith
  -- w0 is within eps0 / |a| of the unit cosine
  have hw_init : Bounded (-(eps0 / |a|)) (eps0 / |a|)
      (fun j => w0 j - Real.cos (k*cell h j)) := by
    intro j
    have e : w0 j - Real.cos (k*cell h j) =
        (computed 0 j - (a*Real.cos (k*cell h j)+b))/a := by
      rw [hw j]
      first | (field_simp; ring) | field_simp
    have hb : |w0 j - Real.cos (k*cell h j)| ≤ eps0 / |a| := by
      rw [e, abs_div]
      exact div_le_div_of_nonneg_right (hinit j) (abs_nonneg a)
    exact abs_le.mp hb
  have hcos := cosine_error_bound D h k (eps0 / |a|) cap T dt w0 hh hD hk hcap0 ht hcap hCFL
    hw_init K hT i
  have hev : evolve D h dt (computed 0) K i = a*evolve D h dt w0 K i + b := by
    rw [hcomp0, evolve_affine]
  have hexact : |evolve D h dt (computed 0) K i - (a*profile D k (cell h i) (elapsed dt K)+b)| ≤
      eps0 + |a| * ((D*h^2*k^4/12 + (D^2*h^2*k^6/12)*cap + (D^3*k^6/6)*cap^2)*T) := by
    rw [hev]
    have h2 := affine_error_bound a b (evolve D h dt w0 K i)
      (profile D k (cell h i) (elapsed dt K)) _ hcos
    have h3 : |a| * (eps0 / |a| + (D*h^2*k^4/12 + (D^2*h^2*k^6/12)*cap + (D^3*k^6/6)*cap^2)*T) =
        eps0 + |a| * ((D*h^2*k^4/12 + (D^2*h^2*k^6/12)*cap + (D^3*k^6/6)*cap^2)*T) := by
      first | (field_simp; ring) | field_simp
    linarith [h2, h3]
  have p1 := abs_le.mp hpert
  have p2 := abs_le.mp hexact
  apply abs_le.mpr
  constructor <;> linarith [p1.1, p1.2, p2.1, p2.2]

theorem harness_error_bound_prefix {n : Nat} (D h k a b eps0 cap T δ : Real) (dt : Nat → Real)
    (computed : Nat → Fin n → Real)
    (hh : 0 < h) (hD : 0 ≤ D) (hk : k*((n : Real)*h) = Real.pi) (ha : a ≠ 0)
    (hcap0 : 0 ≤ cap) (ht : ∀ j, 0 ≤ dt j) (hcap : ∀ j, dt j ≤ cap)
    (hCFL : ∀ j, 2*D*dt j ≤ h*h)
    (hinit : ∀ i, |computed 0 i - (a*Real.cos (k*cell h i)+b)| ≤ eps0)
    (K : Nat)
    (hperturb : ∀ j, j < K → Bounded (-δ) δ
      (fun i => computed (j+1) i - heun D (dt j) h (computed j) i))
    (hT : elapsed dt K ≤ T) (i : Fin n) :
    |computed K i - (a*profile D k (cell h i) (elapsed dt K)+b)| ≤
      eps0 + |a| * ((D*h^2*k^4/12 + (D^2*h^2*k^6/12)*cap + (D^3*k^6/6)*cap^2)*T)
        + (K : Real)*δ :=
  harness_error_bound_of_pert D h k a b eps0 cap T δ dt computed hh hD hk ha hcap0 ht hcap hCFL hinit
    K i (perturbation_only_prefix D h δ dt computed K hh hD ht hCFL hperturb i) hT

/-- Range-closed benchmark bound. `M` is the range in which the per-step implementation premise holds
(for the Gappa bound, M = 2). The side condition `hM` says the exact reference plus the total error
budget stays below M; the theorem derives the range of every computed array by induction. -/
theorem harness_error_bound_ranged {n : Nat} (D h k a b eps0 cap T δ M : Real) (dt : Nat → Real)
    (computed : Nat → Fin n → Real)
    (hh : 0 < h) (hD : 0 ≤ D) (hk : k*((n : Real)*h) = Real.pi) (ha : a ≠ 0)
    (hcap0 : 0 ≤ cap) (ht : ∀ j, 0 ≤ dt j) (hcap : ∀ j, dt j ≤ cap)
    (hCFL : ∀ j, 2*D*dt j ≤ h*h)
    (hinit : ∀ i, |computed 0 i - (a*Real.cos (k*cell h i)+b)| ≤ eps0)
    (K : Nat)
    (hperturb : ∀ j, j < K → (∀ i, |computed j i| ≤ M) → Bounded (-δ) δ
      (fun i => computed (j+1) i - heun D (dt j) h (computed j) i))
    (hT : elapsed dt K ≤ T) (hδ : 0 ≤ δ) (heps : 0 ≤ eps0)
    (hM : |a| + |b| + (eps0 + |a| * ((D*h^2*k^4/12 + (D^2*h^2*k^6/12)*cap + (D^3*k^6/6)*cap^2)*T)
      + (K : Real)*δ) ≤ M)
    (i : Fin n) :
    |computed K i - (a*profile D k (cell h i) (elapsed dt K)+b)| ≤
      eps0 + |a| * ((D*h^2*k^4/12 + (D^2*h^2*k^6/12)*cap + (D^3*k^6/6)*cap^2)*T)
        + (K : Real)*δ := by
  have hTnn : 0 ≤ T := le_trans (elapsed_nonneg dt ht K) hT
  have hbase : 0 ≤ |a| * ((D*h^2*k^4/12 + (D^2*h^2*k^6/12)*cap + (D^3*k^6/6)*cap^2)*T) := by positivity
  have hKδ : 0 ≤ (K : Real)*δ := by positivity
  have hT' : ∀ q, q ≤ K → elapsed dt q ≤ T := fun q hq => le_trans (elapsed_le_of_le dt ht hq) hT
  have hrange0 : ∀ i, |computed 0 i| ≤ M := by
    intro i
    have h1 := abs_le.mp (hinit i)
    have hcb : |Real.cos (k*cell h i)| ≤ 1 := Real.abs_cos_le_one _
    have hac : |a * Real.cos (k*cell h i)| ≤ |a| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg a) hcb
    have h2 := abs_le.mp hac
    have h3 := neg_abs_le b
    have h4 := le_abs_self b
    apply abs_le.mpr
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3, h4, hM, hbase, hKδ, heps]
  have hrange : ∀ j, j ≤ K → ∀ m, m ≤ j → ∀ i, |computed m i| ≤ M := by
    intro j
    induction j with
    | zero =>
      intro hj m hm i
      have h0 : m = 0 := by omega
      subst h0
      exact hrange0 i
    | succ j ih =>
      intro hj m hm i
      by_cases hmj : m ≤ j
      · exact ih (by omega) m hmj i
      · have hm' : m = j + 1 := by omega
        subst hm'
        have hper : ∀ q, q < j+1 → Bounded (-δ) δ
            (fun i => computed (q+1) i - heun D (dt q) h (computed q) i) := by
          intro q hq
          exact hperturb q (by omega) (ih (by omega) q (by omega))
        have hb := harness_error_bound_prefix D h k a b eps0 cap T δ dt computed hh hD hk ha
          hcap0 ht hcap hCFL hinit (j+1) hper (hT' (j+1) hj) i
        have hprof := profile_abs_le_one' D k (cell h i) (elapsed dt (j+1)) hD
          (elapsed_nonneg dt ht (j+1))
        have hap : |a * profile D k (cell h i) (elapsed dt (j+1))| ≤ |a| := by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg a) hprof
        have h1 := abs_le.mp hb
        have h2 := abs_le.mp hap
        have h3 := neg_abs_le b
        have h4 := le_abs_self b
        have hcast : ((j+1 : Nat) : Real) * δ ≤ (K : Real) * δ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ
        apply abs_le.mpr
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3, h4, hcast, hM, heps]
  have hper : ∀ q, q < K → Bounded (-δ) δ
      (fun i => computed (q+1) i - heun D (dt q) h (computed q) i) := by
    intro q hq
    exact hperturb q hq (hrange K le_rfl q (by omega))
  exact harness_error_bound_prefix D h k a b eps0 cap T δ dt computed hh hD hk ha hcap0 ht hcap
    hCFL hinit K hper hT i

end heat_final2

#print axioms heat_final2.perturbed_error_budget_prefix
#print axioms heat_final2.perturbation_only_prefix
#print axioms heat_final2.elapsed_le_of_le
#print axioms heat_final2.profile_abs_le_one'
#print axioms heat_final2.harness_error_bound_of_pert
#print axioms heat_final2.harness_error_bound_prefix
#print axioms heat_final2.harness_error_bound_ranged
