module

import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

section Count

variable (F : Type) [Field F] [NumberField F]

theorem countable_F : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable

theorem sc_Fv (v : HeightOneSpectrum (𝓞 F)) : SecondCountableTopology (v.adicCompletion F) := by
  have := countable_F F
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨_, Set.countable_range _, v.denseRange_algebraMap F⟩
  infer_instance

variable {F} {E : Type} [Field E] [NumberField E] [Algebra F E]

end Count

variable {D : D7}

end Formalism.L2.Fam.ThC

end
