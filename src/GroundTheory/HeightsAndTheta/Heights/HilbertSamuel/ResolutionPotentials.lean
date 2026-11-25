module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionMetricObjects
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgePot
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamStA

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem isPotential_resPot (d : HSMDatum D Ω κ) {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsPotential d.R.A (resPot d m) :=
  AnResBridge.isPotential_potOf d.R (gbamix_smoothHerm_ofCone hm)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
