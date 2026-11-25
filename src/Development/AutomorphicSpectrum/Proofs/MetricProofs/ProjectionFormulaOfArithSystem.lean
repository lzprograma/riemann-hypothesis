module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFIntZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFStep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFVert
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreDim
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystem
public import GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreBij
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreMult
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFHoriz
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFSecRed
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFStep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFVert
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Contract
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixed
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixedField
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArithClosed
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Multilin
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreSum

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv.ProjF

open GroundTheory.Heights₂.Heights

theorem pfIntZero : Inter.PFIntZero.Statement :=
  Inter.PFIntZero.proof (Inter.pointFormRank_holds.proof Inter.RatioAlgDep.proof)

theorem pfVert : Inter.PFVert.Statement :=
  Inter.PFVert.proof (by intros; exact geoNumStatement _) (by intros; exact Targets.ExistsUnique.full _ _)
    Targets.contractMixedField

theorem contractMixed : ContractMixedStatement :=
  Targets.ContractMixed.of_found imageArith Targets.Contract.pulledBackForms_topDensity_vanish
    (Inter.ProjectivePointVertical.proof (by intros; exact geoNumStatement _) (by intros; exact Targets.ExistsUnique.full _ _)
      (by intros; exact Targets.ProjContract.full _ _ _ _ _))
    pfIntZero pfVert

theorem pfStep : Inter.PFStep.Statement :=
  Inter.PFStep.proof (Inter.PFSecRed.proof (by intros; exact Targets.Multilin.full _ _) _root_.GroundTheory.Heights₂.Heights.ForSecondHalf.FibreDim.proof) pfVert pfIntZero
    Inter.PFHoriz.proof (Inter.PFFibreSum.proof _root_.GroundTheory.Heights₂.Heights.ForSecondHalf.FibreDim.proof Inter.PFFibreBij.proof Inter.PFFibreMult.proof)
    imageArith contractMixed

theorem projFormula : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → PFStatement := fun h =>
  Inter.PushforwardProjLineFlag.proof (_root_.GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system h) pfStep

end GlobalTheory.CompanionTheory.Ar.Giv.ProjF
