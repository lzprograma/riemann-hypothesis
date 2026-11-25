module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertRIndexSteps
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CharacterNondegenerate
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertIndex

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial NumberField

noncomputable section

theorem VertRIndex.proof (_hL : LogCardLength.Statement) (hF : SectionQuotFinite.Statement)
    (hV : VertPointLength.Statement) (hR : VertPointResidue.Statement) : VertRIndex.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  obtain ⟨hbij, hmult⟩ := hV T K' y s hP hs hsP
  exact Targets.CurveVertIndex.of_single hP hs hsP (hF T K' y s hP hs hsP) hbij hmult
    (fun W hW => hR T K' y s hP hs hsP W hW)

end

end GroundTheory.Heights₂.Heights
