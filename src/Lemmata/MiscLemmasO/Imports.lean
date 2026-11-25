module

import Lemmata.GeneralBFactAltForm.Imports
public import Mathlib.RingTheory.Localization.FractionRing
import Lemmata.GeneralBFactThirdBisAlt.Imports

@[expose] public section

namespace Bl.SecondBlockLemmaP

theorem goal1 :
  ∀ (O K V : Type) [CommRing.{0} O] [IsDomain.{0} O] [Field.{0} K] [Algebra.{0, 0} O K]
  [IsFractionRing.{0, 0} O K] [AddCommGroup.{0} V] [Module.{0, 0} K V] [Module.{0, 0} O V]
  [IsScalarTower.{0, 0, 0} O K V] (M : Submodule.{0, 0} O V) (v : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} M)) v →
    Exists.{1} fun (c : O) ↦ And (Ne.{1} c 0) (Membership.mem.{0, 0} M (HSMul.hSMul.{0, 0, 0} c v)) :=
  @general_b_fact_third_bis_other.goal1

end Bl.SecondBlockLemmaP
