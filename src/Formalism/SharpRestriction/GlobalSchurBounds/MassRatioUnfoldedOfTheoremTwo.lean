module

public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingNormalisedOfAdjoint
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory

def MassRatioUnderVolume (D : D7) : Prop := StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D

theorem volTie_of_realTied (D : D7) (h : Formalism.L2.Theta.RealTied D) : StandardLattice.VolTie D := by
  intro W P Q hW hs
  have hv := h.vol W hW
  simp only [hs] at hv
  exact hv

variable {eps : ℝ}

end Formalism.MainNotions.RT

end
