-- Concrete positive-normal schedule for the n=400 driver. Each exact is n/d.
namespace HeatSchedule

structure Ratio where
  n : Nat
  d : Nat
deriving DecidableEq

def product (x y : Ratio) : Ratio := ⟨x.n*y.n, x.d*y.d⟩
def quotient (x y : Ratio) : Ratio := ⟨x.n*y.d, x.d*y.n⟩

-- At quantum 2^(-s), select the closer multiple, using the even one on a tie.
def roundAt (x : Ratio) (s : Nat) : Ratio :=
  let a := x.n * 2^s
  let k := a / x.d
  let twice := 2 * (a % x.d)
  let bump := twice > x.d || (twice == x.d && k % 2 == 1)
  ⟨if bump then k+1 else k, 2^s⟩

-- The exact input lies in the claimed binary64 normal binade.
def binade (x : Ratio) (s : Nat) : Bool :=
  x.d > 0 && s <= 1074 && 2^52*x.d <= x.n*2^s && x.n*2^s < 2^53*x.d

def dx := roundAt ⟨6,400⟩ 59
def diffusivity := roundAt ⟨1,100⟩ 59
def factor := roundAt ⟨2,5⟩ 54
def first := roundAt (product factor dx) 60
def numerator := roundAt (product first dx) 66
def denominator := roundAt (product ⟨2,1⟩ diffusivity) 58
def dtMax := roundAt (quotient numerator denominator) 60
def ratio := roundAt (quotient ⟨1,1⟩ dtMax) 45
def count := (ratio.n + ratio.d - 1) / ratio.d
def dt := roundAt ⟨1,count⟩ 60

theorem binades_checked :
  [binade ⟨6,400⟩ 59, binade ⟨1,100⟩ 59, binade ⟨2,5⟩ 54,
   binade (product factor dx) 60, binade (product first dx) 66,
   binade (product ⟨2,1⟩ diffusivity) 58, binade (quotient numerator denominator) 60,
   binade ⟨45,10000⟩ 60, binade (quotient ⟨1,1⟩ dtMax) 45,
   binade ⟨1,count⟩ 60].all id = true := by decide

theorem schedule_checked :
    ((dtMax.n == (roundAt ⟨45,10000⟩ 60).n) &&
     (dtMax.d == (roundAt ⟨45,10000⟩ 60).d) &&
     (222*ratio.d < ratio.n) && (ratio.n < 223*ratio.d) &&
     (count == 223) && (dt.n == 5170051590165233) && (dt.d == 2^60)) = true := by decide
#print axioms binades_checked
#print axioms schedule_checked
end HeatSchedule