module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Formalism.LocalToGlobal.IndefiniteReal.MemSpanOfSmulMem

@[expose] public section

namespace Bl.general_b_fact_second''''''''

theorem goal1 :
  ∀ {K : Type} [Field.{0} K] [NumberField.{0} K] {V : Type} [AddCommGroup.{0} V]
  [Module.{0, 0} K V] [Module.{0, 0} (NumberField.RingOfIntegers.{0} K) V]
  [IsScalarTower.{0, 0, 0} (NumberField.RingOfIntegers.{0} K) K V]
  (M : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) V) {x : V},
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} M)) x →
    Exists.{1} fun (d : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} d 0) (Membership.mem.{0, 0} M (HSMul.hSMul.{0, 0, 0} d x)) :=
  @Formalism.IndefR.LatticeTransfer.Lat.exists_smul_mem

end Bl.general_b_fact_second''''''''
