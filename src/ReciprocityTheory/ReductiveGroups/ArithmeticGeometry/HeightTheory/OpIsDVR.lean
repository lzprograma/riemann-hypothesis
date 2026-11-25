module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField IsLocalRing

theorem Op_isDVR {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : IsDiscreteValuationRing (Op D N la) := by
  apply PI.HtPlacesSumWork.gauss_dvr <;> assumption

end ReciprocityTheory.ChartRestriction.G.T0
