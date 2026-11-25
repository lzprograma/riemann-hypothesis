module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.Finiteness

@[expose] public section

namespace Bl.general_b_fact_left_alt_form

open Formalism.MainNotions.G in
theorem goal1
    {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] [IsDiscreteValuationRing O]
    {W : Type} [inst_3 : AddCommGroup W] [inst_4 : Module (KK O) W] [inst_5 : Module O W]
    [inst_6 : IsScalarTower O (KK O) W] (M : Submodule O W) (y : W) :
    y ∈ MQ (K := KK O) M → ∃ a : O, a ≠ 0 ∧ a • y ∈ M := by
  intro hy
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) (KK O) (M : Set W) y hy
  exact ⟨t, nonZeroDivisors.ne_zero t.2, by simpa only [Submodule.span_eq, Submonoid.smul_def] using ht⟩

end Bl.general_b_fact_left_alt_form
