module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterExtLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedG
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.MetricLocal

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem metricLocal : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement :=
  @GroundTheory.Heights₂.Heights.ForSecondHalf.MetricLocal.full

end GlobalTheory.CompanionTheory.Ar.Giv
