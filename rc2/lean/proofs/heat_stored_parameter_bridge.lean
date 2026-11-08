import proofs.heat_1d

/-! Candidate exact-real bridge for a separately stored denominator q.
Here q may be the real value of fl(h*h). These identities do not prove a
rounding bound, the rounded CFL guard, or execution of the C implementation. -/
namespace heat_1d.FiniteGrid

noncomputable def effectiveDiffusivity (D h q : Real) : Real := D*h*h/q

noncomputable def storedEuler {n : Nat} (D dt q : Real)
    (u : Fin n → Real) : Fin n → Real :=
  fun i => u i + dt * (D * ((u (right i)-2*u i+u (left i))/q))

noncomputable def storedHeun {n : Nat} (D dt q : Real)
    (u : Fin n → Real) : Fin n → Real :=
  fun i => (u i + storedEuler D dt q (storedEuler D dt q u) i)/2

theorem storedEuler_eq {n : Nat} (D dt h q : Real) (u : Fin n → Real)
    (hh : h ≠ 0) (hq : q ≠ 0) :
    storedEuler D dt q u = euler (effectiveDiffusivity D h q) dt h u := by
  funext i
  dsimp [storedEuler, euler, effectiveDiffusivity, heat_1d.discreteSecondDeriv]
  field_simp
  <;> ring

theorem storedHeun_eq {n : Nat} (D dt h q : Real) (u : Fin n → Real)
    (hh : h ≠ 0) (hq : q ≠ 0) :
    storedHeun D dt q u = heun (effectiveDiffusivity D h q) dt h u := by
  unfold storedHeun
  rw [storedEuler_eq D dt h q u hh hq,
    storedEuler_eq D dt h q _ hh hq]
  rfl

theorem effectiveDiffusivity_nonnegative (D h q : Real)
    (hD : 0 ≤ D) (hq : 0 ≤ q) : 0 ≤ effectiveDiffusivity D h q := by
  unfold effectiveDiffusivity
  have hs : 0 ≤ h*h := mul_self_nonneg h
  have hp : 0 ≤ D*(h*h) := mul_nonneg hD hs
  exact div_nonneg (by nlinarith [hp]) hq

theorem effective_CFL (D dt h q : Real) (hq : 0 < q)
    (hbound : 2*D*dt ≤ q) :
    2*effectiveDiffusivity D h q*dt ≤ h*h := by
  have heq : 2*effectiveDiffusivity D h q*dt = (2*D*dt/q)*(h*h) := by
    unfold effectiveDiffusivity
    ring
  have hr : 2*D*dt/q ≤ 1 := (div_le_iff₀ hq).mpr (by simpa using hbound)
  rw [heq]
  simpa using mul_le_mul_of_nonneg_right hr (mul_self_nonneg h)

theorem effective_decay_coefficient (D h q cells elapsed : Real)
    (hh : h ≠ 0) (hc : cells ≠ 0) (hq : q ≠ 0) :
    effectiveDiffusivity D h q * elapsed / (cells*h)^2 =
      D * elapsed / (q*cells^2) := by
  unfold effectiveDiffusivity
  field_simp
  <;> ring

end heat_1d.FiniteGrid
#print axioms heat_1d.FiniteGrid.storedHeun_eq
#print axioms heat_1d.FiniteGrid.effective_CFL
#print axioms heat_1d.FiniteGrid.effective_decay_coefficient
