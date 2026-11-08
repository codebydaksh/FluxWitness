import proofs.heat_rounded_benchmark
import proofs.heat_bounded_arithmetic

namespace heat_rounding
noncomputable section

open heat_1d.FiniteGrid heat_grid_bridge heat_reference

theorem verified_benchmark
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
    (heps1 : eps0 <= (24854 / 100000000000000000000 : Real))
    (hinit : forall i, |u0 i - (1/2 * Real.cos (k*cell h i)+1)| <= eps0)
    (i : Fin 400) :
    |roundedEvolution (arithmeticFromBoundedLaws 1000000 (1/9007199254740992) (1/10^30) round half (by norm_num) (by norm_num) hr hh) (fun _ => dt) u0 223 i -
      (1/2 * profile D k (cell h i) (((223 : Nat) : Real)*dt)+1)| <=
      (705 / 100000000000 : Real) := by
  
  let a := arithmeticFromBoundedLaws 1000000 (1/9007199254740992) (1/10^30) round half (by norm_num) (by norm_num) hr hh
  
  -- Using rfl instead of simp to avoid structure projection issues
  apply abstract_rounded_benchmark a (by rfl) (by rfl) D h k dt eps0 u0 hD_eq hh0 hh1 hD0 hD1 hdt0 hdt1 hk heps0 heps1 hinit i

end
end heat_rounding

#print axioms heat_rounding.verified_benchmark