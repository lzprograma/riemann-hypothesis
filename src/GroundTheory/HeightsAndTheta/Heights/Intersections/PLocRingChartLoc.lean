module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingChartLoc
public import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingNoeth
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingChartLoc.proof : LocRingChartLoc.Statement := fun K _ ι _ P W hP hW hPW hrel =>
  LocRingNoeth.exists_chart_loc LocRingFrac.proof K ι P W hP hW hPW hrel

end

end GroundTheory.Heights₂.Heights.Inter
