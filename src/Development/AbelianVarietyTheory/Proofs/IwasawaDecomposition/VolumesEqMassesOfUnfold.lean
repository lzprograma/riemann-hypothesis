module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoubleCosetsMassLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll
public import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.VolMass

theorem volumes_eq_masses_of_unfold :
    (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) → ∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D :=
  fun hU D hV =>
    have hT : StandardLattice.VolTie D := Formalism.L2.Theta.VolTieG.volTie hV
    StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D (hU D hT))
      (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.mass_volume_identity_of_class_decomp D hT (_root_.GlobalTheory.genusMassStd D)
        (_root_.GlobalTheory.DefiniteDecomp.defClassDecomp D))

end GlobalTheory.Mem.VolMass
