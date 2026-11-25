module

import Lemmata.GeneralBFactAltForm.Imports
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace Bl.general_b_fact_third'''''

theorem goal1 :
  ∀ {E : Type} [Field.{0} E] [NumberField.{0} E] {V : Type} [AddCommGroup.{0} V]
  [Module.{0, 0} E V] [Module.{0, 0} (NumberField.RingOfIntegers.{0} E) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E V]
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) V),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} Λ)) Top.top.{0} →
    ∀ (x : V),
      Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} d 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} d x)) := by
  intro E _ _ V _ _ _ _ Λ hspan x
  exact Bl.general_b_fact_alt_form.goal1 (F := E) Λ (x := x) (by rw [hspan]; exact Submodule.mem_top)

end Bl.general_b_fact_third'''''
