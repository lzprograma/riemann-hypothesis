module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

@[expose] public section

noncomputable section
open Classical Polynomial

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.BasicNotions Formalism.MainNotions NumberField

theorem exists_skew (D : D7) : letI := D.host.cmStar; ∃ s : D.host.E, star s = -s ∧ s ≠ 0 := by
  letI := D.host.cmStar
  haveI := D.host.isCMField_hostE
  by_contra hno
  push Not at hno
  apply NumberField.IsCMField.complexConj_ne_one D.host.E
  refine AlgEquiv.ext fun x => ?_
  have h := hno (x - star x) (by rw [star_sub, star_star]; ring)
  exact (sub_eq_zero.mp h).symm

end Formalism.L2.PairingIndexBounds.Eq.J
