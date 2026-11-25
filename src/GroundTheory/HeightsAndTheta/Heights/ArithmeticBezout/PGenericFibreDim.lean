module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Algebra.Order.AddGroupWithTop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

namespace GenericFibreDim

theorem eq_natCast_of_add_one_eq (d : ℕ) (x : WithBot ℕ∞)
    (hform : x + 1 = ((d : ℕ) : WithBot ℕ∞) + 1) : x = d :=
  ENat.WithBot.add_one_cancel.mp hform

end GenericFibreDim


end ObjectsChow

end GroundTheory.Heights₂.Heights
