module

import Lemmata.GeneralBFactAltForm.Imports
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace Bl.general_b_fact_left''''''''

theorem goal1 :
  ∀ {K V : Type} [Field.{0} K] [NumberField.{0} K] [AddCommGroup.{0} V] [Module.{0, 0} K V]
  [Module.{0, 0} (NumberField.RingOfIntegers.{0} K) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K V]
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) V) (v : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} L)) v →
    Exists.{1} fun (d : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} d 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} d v)) := by
  intro K V _ _ _ _ _ _ L v hv
  exact Bl.general_b_fact_alt_form.goal1 (F := K) L (x := v) hv

end Bl.general_b_fact_left''''''''
