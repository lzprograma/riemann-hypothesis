module

import Lemmata.GeneralBFactAltForm.Imports
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

namespace Bl.general_b_fact_second''

theorem goal1 :
  ∀ {O K X : Type} [CommRing.{0} O] [IsDomain.{0} O] [Field.{0} K] [Algebra.{0, 0} O K]
  [IsFractionRing.{0, 0} O K] [AddCommGroup.{0} X] [Module.{0, 0} K X] [Module.{0, 0} O X]
  [IsScalarTower.{0, 0, 0} O K X] (B : Submodule.{0, 0} O X),
  Eq.{1} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} B)) Top.top.{0} →
    ∀ (x : X), Exists.{1} fun (d : O) ↦ And (Ne.{1} d 0) (Membership.mem.{0, 0} B (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro O K X _ _ _ _ _ _ _ _ _ B hB x
  exact Bl.general_b_fact_alt_form.goal1 (F := K) B (by simp [hB])

end Bl.general_b_fact_second''
