module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable

@[expose] public section

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem ptsIntegrable_of_resK :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → PtsIntegrableStatement :=
  fun h => GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists (GlobalTheory.T.resolution_exists_of_resolution_statement h)

end GlobalTheory.CompanionTheory.Ar.Giv
