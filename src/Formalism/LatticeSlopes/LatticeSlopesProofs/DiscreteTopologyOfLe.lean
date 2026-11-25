module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace Formalism.F

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem discreteTopology_of_le {L N : Submodule ℤ E} (h : N ≤ L) [hL : DiscreteTopology L] :
    DiscreteTopology N :=
  DiscreteTopology.of_continuous_injective (f := Submodule.inclusion h)
    (continuous_subtype_val.subtype_mk _) (Submodule.inclusion_injective h)

end Formalism.F
