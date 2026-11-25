module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

variable {D : D7}

open GlobalTheory.IndefiniteRowSideFullHecke

instance topRing (D : D7) : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _

end GlobalTheory.DualPairCompare

end
