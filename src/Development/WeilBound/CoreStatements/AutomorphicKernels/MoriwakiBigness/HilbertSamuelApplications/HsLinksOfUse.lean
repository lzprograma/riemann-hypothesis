module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.SmallGeneratedCountUpperOfUse
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsDimX
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsZhangLowerX
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PZhangLowerX
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.RingKrullDimLocalizationInt
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.BigLineBundleMoriwaki
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Imports
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.ImportsBis

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open ReciprocityTheory.ChartRestriction.G.Geo

theorem hsLinks_of_use :
    PositivityTheory.MbHsUse.HSUse → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement →
      ArithmeticIntersectionNonneg ∧ SuccessiveMinimaLowerBound ∧ SuccessiveMinimaUpperBound ∧ ArithmeticVolumeLowerBound ∧
        GroundTheory.Heights₂.Heights.LowerBoundFree.ZhangLowerX.Statement ∧ GroundTheory.Heights₂.Heights.DimX.Statement := by
  intro hU hBig
  have a0 : SuccessiveMinimaLowerBound := hU.z1
  exact ⟨GroundTheory.Heights₂.Heights.ForSecondHalf.G1.full, a0,
    GroundTheory.Heights₂.Heights.ForSecondHalf.Z2.proof hBig,
    GroundTheory.Heights₂.Heights.ForSecondHalf.BigLineBundleMoriwaki.of_moriwakiBig hBig,
    GroundTheory.Heights₂.Heights.LowerBoundFree.ZhangLowerX.proof a0,
    GroundTheory.Heights₂.Heights.DimX.proof⟩

end GlobalTheory.CompanionTheory.Ar.Giv
