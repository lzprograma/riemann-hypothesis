module

import Lemmata.GeneralBFactAltForm.Imports
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace Bl.general_b_fact_third_ter

theorem goal1 :
  ∀ {E : Type} [Field.{0} E] [NumberField.{0} E] [StarRing.{0} E] {W : Type} [AddCommGroup.{0} W]
  [Module.{0, 0} E W] [Module.{0, 0} (NumberField.RingOfIntegers.{0} E) W]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E W]
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) W),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L)) Top.top.{0} →
    ∀ (y : W),
      Exists.{1} fun (ν : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} ν 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} ν y)) := by
  intro E _ _ _ W _ _ _ _ L hL y
  exact Bl.general_b_fact_alt_form.goal1 (F := E) L (x := y) (by rw [hL]; exact Submodule.mem_top)

end Bl.general_b_fact_third_ter
