module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulMemSpanIntegers
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace Bl.general_b_fact_right_alt_form

theorem goal1 :
  ∀ {E : Type} [Field.{0} E] [NumberField.{0} E] {V : Type} [AddCommGroup.{0} V]
  [Module.{0, 0} E V] [Module.{0, 0} (NumberField.RingOfIntegers.{0} E) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E V] (A : Set.{0} V) (y : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} E A) y →
    Exists.{1} fun (d : NumberField.RingOfIntegers.{0} E) ↦
      And (Ne.{1} d 0)
        (Membership.mem.{0, 0} (Submodule.span.{0, 0} (NumberField.RingOfIntegers.{0} E) A) (HSMul.hSMul.{0, 0, 0} d y)) := by
  apply GlobalTheory.SmulMemSpanIntegers.exists_smul_mem_span_integers

end Bl.general_b_fact_right_alt_form
