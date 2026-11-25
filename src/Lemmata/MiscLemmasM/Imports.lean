module

public import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele

@[expose] public section

namespace Bl.SecondBlockLemmaN

theorem goal1 :
  ∀ (z : Complex),
  (∀ (n : Nat), LT.lt.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} z n) 1)) (1 / 2)) → Eq.{1} z 1 :=
  @GlobalTheory.CuspRep.eq_one_of_pow_near

end Bl.SecondBlockLemmaN
