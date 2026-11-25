module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.SAOpenStatement
public import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Assembly

@[expose] public section

namespace PositivityTheory.EqVol

theorem sa : ReciprocityTheory.ChartRestriction.G.SA.SAStatement := GroundTheory.Heights₂.Heights.StrongApprox.SAHolds.full

end PositivityTheory.EqVol
