module

import Lemmata.GeneralBFactAltForm.Imports
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace Bl.general_b_fact_third_form

theorem goal1 :
  ∀ {E V : Type} [Field.{0} E] [NumberField.{0} E] [StarRing.{0} E] [AddCommGroup.{0} V]
  [Module.{0, 0} E V] [FiniteDimensional.{0, 0} E V]
  [Module.{0, 0} (NumberField.RingOfIntegers.{0} E) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} E) E V]
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) V) [Submodule.IsFullLattice.{0, 0, 0} E Λ] (v : V),
  Exists.{1} fun (s : NumberField.RingOfIntegers.{0} E) ↦
    And (Ne.{1} s 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} s v)) := by
  intro E V _ _ _ _ _ _ _ _ Λ hΛ v
  exact Bl.general_b_fact_alt_form.goal1 (F := E) Λ (x := v) (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)

end Bl.general_b_fact_third_form
