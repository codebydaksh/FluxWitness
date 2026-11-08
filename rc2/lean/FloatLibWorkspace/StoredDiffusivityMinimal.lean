import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel.MulDiv
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.BinaryInterchange.Model.RealSemantics
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace FluxWitnessR1
open FloatLib.Floats.Formats.BinaryInterchange

theorem binary64_bitWidth : FloatFormat.binary64.bitWidth = 64 := by rfl
theorem binary64_isIEEE : FloatFormat.binary64.isIEEE = true := by decide

/-- Embedding of a native `Float` into FloatLib's binary64 `Model` through its packed bits. -/
def asLib (f : Float) : Model FloatFormat.binary64 :=
  Model.ofBits (fmt := FloatFormat.binary64)
    (BitVec.cast binary64_bitWidth.symm f.toBits.toBitVec)

theorem bridge_direct_div (a b : Float) :
    asLib (a / b) = Model.ofModel FloatFormat.binary64
      (Float.Model.UnpackedFloat.div (FloatFormat.toModel FloatFormat.binary64)
        (Model.toModel (asLib a)) (Model.toModel (asLib b))) := rfl

theorem native_div_rounding (a b : Float)
    (hb : Model.isFinite (asLib b) = true)
    (hfin : Model.isFinite (asLib (a / b)) = true) :
    Model.toReal (asLib (a / b))
      = Model.roundAt FloatFormat.binary64
          (Model.toReal (asLib a) / Model.toReal (asLib b)) := by
  have h := bridge_direct_div a b
  rw [h] at hfin
  rw [h]
  exact Model.toReal_ofModel_div_toModel_eq_roundAt binary64_isIEEE (asLib a) (asLib b) hb hfin


end FluxWitnessR1
namespace FloatLib.Floats.Formats.BinaryInterchange.Model
open FluxWitnessR1
theorem fw_D001_dyadic :
    toDyadic? (asLib (0.01 : Float)) = some
      { negative := false, significand := 5764607523034235, exponent := -59 } := by
  rfl

theorem fw_toReal_D001 :
    toReal (asLib (0.01 : Float)) = 5764607523034235 / 576460752303423488 := by
  rw [toReal_eq, fw_D001_dyadic]
  norm_num [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]


-- Use the division theorem at 1/100. The division's stored dyadic is the
-- same as the literal's stored dyadic. This avoids assuming decimal exactness.
theorem stored_diffusivity_A6 :
    toReal (asLib (0.01 : Float)) = roundAt FloatFormat.binary64 (1 / 100 : Real) := by
  have oneBits : toDyadic? (asLib (1.0 : Float)) = some
      { negative := false, significand := 4503599627370496, exponent := -52 } := by rfl
  have hundredBits : toDyadic? (asLib (100.0 : Float)) = some
      { negative := false, significand := 7036874417766400, exponent := -46 } := by rfl
  have oneReal : toReal (asLib (1.0 : Float)) = 1 := by
    rw [toReal_eq, oneBits]
    norm_num [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]
  have hundredReal : toReal (asLib (100.0 : Float)) = 100 := by
    rw [toReal_eq, hundredBits]
    norm_num [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand]
  have quotientBits : toDyadic? (asLib ((1.0 : Float) / 100.0)) = some
      { negative := false, significand := 5764607523034235, exponent := -59 } := by rfl
  have equalReal : toReal (asLib (0.01 : Float)) =
      toReal (asLib ((1.0 : Float) / 100.0)) := by
    simp only [toReal_eq, fw_D001_dyadic, quotientBits]
  have h := native_div_rounding (1.0 : Float) (100.0 : Float) (by rfl) (by rfl)
  rw [oneReal, hundredReal] at h
  exact equalReal.trans h

end FloatLib.Floats.Formats.BinaryInterchange.Model

#print axioms FloatLib.Floats.Formats.BinaryInterchange.Model.fw_toReal_D001
#print axioms FloatLib.Floats.Formats.BinaryInterchange.Model.stored_diffusivity_A6