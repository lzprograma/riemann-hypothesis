module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EpEqOneIff

@[expose] public section

namespace Bl.general_b_fact_right_side

/-- `exp (2 π i x) = 1` if and only if the real number `x` is an integer. -/
theorem goal1 (x : Real) :
    Complex.exp (2 * Complex.ofReal Real.pi * Complex.I * Complex.ofReal x) = 1 ↔
      ∃ n : Int, x = n := UpperTheory.Reformulated.B.Qj15.ep_eq_one_iff x

end Bl.general_b_fact_right_side
