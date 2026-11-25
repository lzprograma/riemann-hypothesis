module

public import Mathlib.FieldTheory.IsSepClosed
public import GroundTheory.ProfiniteCohomology.DiscreteModules
import GroundTheory.ProfiniteCohomology.OpenNormal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.Topology.Algebra.Group.Defs

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open CategoryTheory groupCohomology GroundTheory.ProfCoh

universe u

section Main

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]

instance isSepClosure_intermediateField (E : IntermediateField K Ks) : IsSepClosure E Ks :=
  ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K E Ks⟩

variable (E : IntermediateField K Ks)

end Main

end GroundTheory.Brauer
