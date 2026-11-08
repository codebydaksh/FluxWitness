import C2DecodedStep
import BenchmarkNativeHalf
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Finiteness

namespace FluxWitnessC4
open FloatLib FloatLib.Floats.Formats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.FloatFormat
open heat_rounding heat_1d.FiniteGrid FluxWitness400

private theorem representative {x : ℝ} (hx : Model.roundAt binary64 x = x) (hb : |x| ≤ 2) :
    ∃ v : Model binary64, Model.isFinite v = true ∧ Model.toReal v = x := by
  have hg := Model.genericFormat_roundAt binary64 x
  rw [hx] at hg
  let m := ⌊Flocq.scaledMantissa Numerics.binaryRadix (Model.fexpOf binary64) x⌋
  let e := Flocq.cexp Numerics.binaryRadix (Model.fexpOf binary64) x
  have hm : x = (m : ℝ) * (2 : ℝ)^e := hg
  have hd (z : ℤ) : ∃ d : Numerics.Dyadic, d.toReal = (z : ℝ) * (2:ℝ)^e := by
    cases z with
    | ofNat n => exact ⟨⟨false,n,e⟩, rfl⟩
    | negSucc n =>
      refine ⟨⟨true,n+1,e⟩, ?_⟩
      rfl
  obtain ⟨d, hdval⟩ := hd m
  have he := hdval.trans hm.symm
  have hmax : (2:ℝ) ≤ Model.toReal (Model.posMaxFinite binary64) := by
    have h := Model.abs_signed_mul_bpow_le_toReal_posMaxFinite
      binary64 false 2 0 (by decide) (by decide)
    simpa [Model.bpow_zero] using h
  have hf := Model.isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite
    binary64 (by decide) d (by rw [he]; exact hb.trans hmax)
  refine ⟨_, hf, ?_⟩
  rw [Model.toReal_roundDyadic_eq_roundAt binary64 (by decide) d hf, he, hx]

theorem reference223 (v0 : Fin 400 → Model binary64)
    (hf : ∀ i, Model.isFinite (v0 i) = true)
    (hi : ∀ i, |Model.toReal (v0 i) -
      (1/2 * Real.cos (Real.pi * (2 * (i.val : ℝ) + 1) / 800) + 1)| ≤ initialBudget) :
    let u := roundedEvolution c1Arithmetic (fun _ => stepTime) (fun i => Model.toReal (v0 i))
    ∃ ref : Nat → Fin 400 → Model binary64, ref 0 = v0 ∧
      (∀ k ≤ 223, ∀ i, Model.isFinite (ref k i) = true ∧
        Model.toReal (ref k i) = u k i ∧ |Model.toReal (ref k i)| ≤ 2) ∧
      ∀ k < 223, ∀ i, Model.toReal (ref (k+1) i) =
        FluxWitnessC2.interpretedStep (fun j => Model.toReal (ref k j)) stepTime i := by
  let u0 := fun i => Model.toReal (v0 i)
  let u := roundedEvolution c1Arithmetic (fun _ => stepTime) u0
  have initRange : Bounded (-(151/100)) (151/100) u0 := by
    intro i
    have h := abs_le.mp (hi i)
    unfold initialBudget at h
    change -(151/100) ≤ Model.toReal (v0 i) ∧ Model.toReal (v0 i) ≤ 151/100
    constructor <;> linarith only [Real.neg_one_le_cos (Real.pi * (2 * (i.val : ℝ) + 1) / 800),
      Real.cos_le_one (Real.pi * (2 * (i.val : ℝ) + 1) / 800), h.1, h.2]
  have cap : |stepTime| ≤ 9/2000 := by norm_num [stepTime]
  have bound (k : Nat) (hk : k ≤ 223) (i : Fin 400) : |u k i| ≤ 2 :=
    abs_le.mpr ((roundedEvolution_error_and_range c1Arithmetic rfl rfl spacing (151/100)
      (by norm_num [spacing]) (fun _ => stepTime) u0 223
      (fun _ => by norm_num [stepTime]) (fun _ => cap)
      (fun _ => by norm_num [effectiveDiffusivity, storedD, spacing, storedQ, stepTime])
      initRange (by norm_num [roundingDelta]) k hk).2 i)
  have fixed (k : Nat) (hk : k ≤ 223) : ∀ i, Model.roundAt binary64 (u k i) = u k i := by
    induction k with
    | zero => exact fun i => Model.roundAt_toReal_eq (v0 i) (hf i)
    | succ k ih =>
      intro i
      change Model.roundAt binary64 (roundedStep c1Arithmetic storedD stepTime storedQ (u k) i) =
        roundedStep c1Arithmetic storedD stepTime storedQ (u k) i
      rw [boundedStep_eq_explicit_rounded (u k) stepTime (bound k (by omega)) (ih (by omega)) cap i]
      unfold c1ExplicitStep
      exact Model.roundAt_of_genericFormat binary64 (Model.genericFormat_roundAt binary64 _)
  classical
  have witness (k : Nat) (hk : k ≤ 223) (i : Fin 400) :=
    representative (fixed k hk i) (bound k hk i)
  let ref : Nat → Fin 400 → Model binary64 := fun k i =>
    if k = 0 then v0 i else if h : k ≤ 223 then (witness k h i).choose else v0 i
  have spec (k : Nat) (hk : k ≤ 223) (i : Fin 400) :
      Model.isFinite (ref k i) = true ∧ Model.toReal (ref k i) = u k i := by
    by_cases hz : k = 0
    · subst k
      exact ⟨by simpa [ref] using hf i, by simp [ref,u,roundedEvolution,u0]⟩
    · simpa [ref,hz,hk] using (witness k hk i).choose_spec
  refine ⟨ref, by funext i; simp [ref], fun k hk i =>
    ⟨(spec k hk i).1, (spec k hk i).2, (spec k hk i).2.symm ▸ bound k hk i⟩, ?_⟩
  intro k hk i
  rw [(spec (k+1) (by omega) i).2, FluxWitnessC2.decoded_step_agrees (ref k) stepTime
    (fun j => (spec k (by omega) j).1)
    (fun j => by rw [(spec k (by omega) j).2]; exact bound k (by omega) j) cap i]
  rw [show (fun j => Model.toReal (ref k j)) = u k from funext (fun j => (spec k (by omega) j).2)]
  rfl

end FluxWitnessC4
#print axioms FluxWitnessC4.reference223
