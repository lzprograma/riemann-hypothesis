module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Imports
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace Bl.general_b_fact_second'

theorem goal1 :
  ∀ {E U : Type} [Field.{0} E] [NumberField.{0} E] [AddCommGroup.{0} U] [Module.{0, 0} E U]
  [Module.{0, 0} (NumberField.RingOfIntegers.{0} E) U]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E U]
  (N : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) U),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} N)) Top.top.{0} →
    ∀ (x : U),
      Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} d 0) (Membership.mem.{0, 0} N (HSMul.hSMul.{0, 0, 0} d x)) := by
  apply GlobalTheory.TargetStatementBis.main

end Bl.general_b_fact_second'
