module

import Lemmata.GeneralBFactThirdBisAlt.Imports
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

namespace Bl.SecondBlockLemmaK

theorem goal1 :
  ∀ {R F X : Type} [CommRing.{0} R] [IsDomain.{0} R] [Field.{0} F] [Algebra.{0, 0} R F]
  [IsFractionRing.{0, 0} R F] [AddCommGroup.{0} X] [Module.{0, 0} F X] [Module.{0, 0} R X]
  [IsScalarTower.{0, 0, 0} R F X] (S : Submodule.{0, 0} R X) {x : X},
  Membership.mem.{0, 0} (Submodule.span.{0, 0} F (SetLike.coe.{0, 0} S)) x →
    Exists.{1} fun (d : R) ↦ And (Ne.{1} d 0) (Membership.mem.{0, 0} S (HSMul.hSMul.{0, 0, 0} d x)) :=
  general_b_fact_third_bis_other.goal1

end Bl.SecondBlockLemmaK
