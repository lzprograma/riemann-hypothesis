module

import Lemmata.GeneralBFactAltForm.Imports
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace Bl.general_b_fact_second_form

theorem goal1 :
  ∀ {K V : Type} [Field.{0} K] [NumberField.{0} K] [StarRing.{0} K] [AddCommGroup.{0} V]
  [Module.{0, 0} K V] [Module.{0, 0} (NumberField.RingOfIntegers.{0} K) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K V]
  {Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) V},
  Submodule.IsFullLattice.{0, 0, 0} K Λ →
    ∀ (v : V),
      Exists.{1} fun (r : NumberField.RingOfIntegers.{0} K) ↦
        And (Ne.{1} r 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} r v)) := by
  intro K V _ _ _ _ _ _ _ Λ hΛ v
  exact Bl.general_b_fact_alt_form.goal1 (F := K) Λ (x := v) (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)

end Bl.general_b_fact_second_form
