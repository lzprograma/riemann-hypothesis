module

import Lemmata.GeneralBFactSecond.Imports
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace Bl.general_b_fact_left_bis

theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] {N : Nat}
  (L'' : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) (Fin N → E)),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L'')) Top.top.{0} →
    ∀ (v : Fin N → E),
      Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} d 0) (Membership.mem.{0, 0} L'' (HSMul.hSMul.{0, 0, 0} d v)) := by
  exact Bl.general_b_fact_second.goal1

end Bl.general_b_fact_left_bis
