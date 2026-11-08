import proofs.heat_1d

/-! Candidate finite-horizon range bootstrap. No C or floating-point bound is
asserted here: the local implementation estimate is an explicit premise,
required only when the current state lies in its certified range. -/
namespace heat_1d.FiniteGrid

theorem range_from_error {n : Nat} (M E R : Real) (u v : Fin n → Real)
    (hv : Bounded (-M) M v)
    (he : Bounded (-E) E (fun i => u i - v i))
    (hmargin : M + E ≤ R) : Bounded (-R) R u := by
  intro i
  obtain ⟨vlo, vhi⟩ := hv i
  obtain ⟨elo, ehi⟩ := he i
  constructor <;> linarith

/-- Error propagation and range closure without assuming the conclusion in the
local rounding hypothesis. Only the finite prefix j < K is required. -/
theorem finite_range_bootstrap {n : Nat} (D h eps δ M R : Real)
    (dt : Nat → Real) (computed reference : Nat → Fin n → Real) (K : Nat)
    (hh : 0 < h) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (ht : ∀ j, j < K → 0 ≤ dt j)
    (hCFL : ∀ j, j < K → 2*D*dt j ≤ h*h)
    (href : ∀ j, j < K → reference (j+1) = heun D (dt j) h (reference j))
    (href_range : ∀ j, j ≤ K → Bounded (-M) M (reference j))
    (hinit : Bounded (-eps) eps (fun i => computed 0 i-reference 0 i))
    (hmargin : M + (eps + (K : Real)*δ) ≤ R)
    (hlocal : ∀ j, j < K → Bounded (-R) R (computed j) →
      Bounded (-δ) δ (fun i => computed (j+1) i-heun D (dt j) h (computed j) i)) :
    ∀ j, j ≤ K →
      Bounded (-(eps + (j : Real)*δ)) (eps + (j : Real)*δ)
        (fun i => computed j i-reference j i) ∧ Bounded (-R) R (computed j) := by
  have margin : ∀ j, j ≤ K → M + (eps + (j : Real)*δ) ≤ R := by
    intro j hj
    have hjr : (j : Real) ≤ (K : Real) := by exact_mod_cast hj
    have hp := mul_le_mul_of_nonneg_right hjr hδ
    linarith
  intro j
  induction j with
  | zero =>
    intro hj
    have he : Bounded (-(eps + ((0 : Nat) : Real)*δ)) (eps + ((0 : Nat) : Real)*δ)
        (fun i => computed 0 i-reference 0 i) := by simpa using hinit
    exact ⟨he, range_from_error M _ R _ _ (href_range 0 hj) he (margin 0 hj)⟩
  | succ j ih =>
    intro hj
    have hjlt : j < K := by omega
    have hjle : j ≤ K := by omega
    obtain ⟨he, hr⟩ := ih hjle
    have hs := heun_difference_bounded D (dt j) h (eps + (j : Real)*δ)
      (computed j) (reference j) hh hD (ht j hjlt) (hCFL j hjlt) he
    have hl := hlocal j hjlt hr
    have hn : Bounded (-(eps + ((j+1 : Nat) : Real)*δ))
        (eps + ((j+1 : Nat) : Real)*δ)
        (fun i => computed (j+1) i-reference (j+1) i) := by
      intro i
      obtain ⟨slo, shi⟩ := hs i
      obtain ⟨llo, lhi⟩ := hl i
      rw [href j hjlt]
      push_cast
      constructor <;> linarith
    exact ⟨hn, range_from_error M _ R _ _ (href_range (j+1) hj) hn (margin (j+1) hj)⟩

end heat_1d.FiniteGrid
#print axioms heat_1d.FiniteGrid.finite_range_bootstrap
