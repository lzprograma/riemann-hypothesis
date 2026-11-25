module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointChart

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

theorem VertPointChart.proof (hC : CurveCharts.Statement) : VertPointChart.Statement := by
  intro T _ K' _ _ y s hy hs hsP W hW t ht
  have hCB := hC T K' y hy
  obtain ⟨hmax, hrat, hiff⟩ := Targets.CurveVertPointChart.of_single hy hs hsP hCB.1
    (fun m hm => by
      obtain ⟨t', hyt', h'⟩ := hCB.2.2 m hm
      exact ⟨fun _ => t', fun _ => hyt', fun ⟨(), u⟩ => h' u⟩)
    hW (fun _ => t) (fun _ => ht)
  refine ⟨hmax, fun u => hrat ⟨(), u⟩, fun d g hg => ?_⟩
  simpa only [Fintype.prod_unique] using hiff (fun _ => d) g hg

end

end GroundTheory.Heights₂.Heights
