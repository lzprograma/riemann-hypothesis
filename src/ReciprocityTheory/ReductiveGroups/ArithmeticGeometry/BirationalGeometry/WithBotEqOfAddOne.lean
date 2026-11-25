module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
public import Mathlib.Data.ENat.Basic

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem withBot_eq_of_add_one {a : WithBot ℕ∞} {n : ℕ}
    (h : a + 1 = ((n + 1 : ℕ) : WithBot ℕ∞)) : a = (n : WithBot ℕ∞) := by
  apply ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one <;> assumption

end ReciprocityTheory.ChartRestriction.G.Geo
