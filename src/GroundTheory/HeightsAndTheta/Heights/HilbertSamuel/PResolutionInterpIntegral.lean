module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionInterpIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionPotentials
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionInterpIntegral
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamStA

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology

noncomputable section

namespace ResolutionInterpIntegral

theorem proof : ResolutionInterpIntegral.Statement := by
  intro D Ω _ _ κ _ d m₁ hm₁
  exact BlockResolutionInterpIntegral.interp_integral_eq d.R (A₀ := HermLine.ofCone d.m)
    (A₁ := HermLine.ofCone m₁) rfl (gbamix_smoothHerm_ofCone d.smooth) (gbamix_smoothHerm_ofCone hm₁)
    (fun t => resPot d (interp d.m m₁ t)) fun t x y hy => by
      have hz : d.R.lift x y ≠ 0 := gaamix_ne_zero_of_mcPts (d.R.mem x y hy)
      show Real.log (d.m.ρ (d.R.lift x y) ^ (1 - t) * m₁.ρ (d.R.lift x y) ^ t) =
        (1 - t) * Real.log (d.m.ρ (d.R.lift x y)) + t * Real.log (m₁.ρ (d.R.lift x y))
      rw [Real.log_mul (Real.rpow_pos_of_pos (d.m.pos _ hz) _).ne'
        (Real.rpow_pos_of_pos (m₁.pos _ hz) _).ne',
        Real.log_rpow (d.m.pos _ hz), Real.log_rpow (m₁.pos _ hz)]

end ResolutionInterpIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
