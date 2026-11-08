import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof
import FloatLib.Floats.Formats.Flocq.Theory.Format.Magnitude

namespace FluxWitnessC2
open FloatLib FloatLib.Floats.Formats
open BinaryInterchange

-- e is specified by inequalities, without choosing an implementation of log2.
noncomputable def floorEvenGrid (e : ℤ) (x : ℝ) : ℝ :=
  let k := max (e - 53) (-1074)
  let y := x * Flocq.bpow Numerics.binaryRadix (-k)
  let n : ℤ := ⌊y⌋
  let m : ℤ := if y - n < 1/2 then n else if y - n > 1/2 then n+1
               else if Even n then n else n+1
  (m : ℝ) * Flocq.bpow Numerics.binaryRadix k

theorem binary64_floorEvenGrid (x : ℝ) (e : ℤ) (hx : x ≠ 0)
    (hl : Flocq.bpow Numerics.binaryRadix (e-1) ≤ |x|)
    (hu : |x| < Flocq.bpow Numerics.binaryRadix e) :
    Model.roundAt FloatFormat.binary64 x = floorEvenGrid e x := by
  have hm := Flocq.magnitude_eq_of_bpow_bounds Numerics.binaryRadix x e hx hl hu
  change floorEvenGrid (Flocq.magnitude Numerics.binaryRadix x) x = floorEvenGrid e x
  rw [hm]

theorem binary64_round_zero : Model.roundAt FloatFormat.binary64 0 = 0 := by
  exact Model.roundAt_zero FloatFormat.binary64

#print axioms binary64_floorEvenGrid
#print axioms binary64_round_zero
end FluxWitnessC2
