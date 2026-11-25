module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointInj
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

theorem VertPointInj.proof (hCh : VertPointChart.Statement) : VertPointInj.Statement := by
  intro T _ K' _ _ y s hA hs hsP W hW W' hW' hWW'
  exact Targets.CurveVertPointInj.of_single (K := Unit) (ι := fun _ => T) y s (fun _ => 1)
    hA hs W hW W' hW' hWW' fun W₀ hW₀ c hc => by
      obtain ⟨hmax, hrat, hform⟩ := hCh T K' y s hA hs hsP W₀ hW₀ (c ()) (hc ())
      refine ⟨hmax, fun p => hrat p.2, fun e g hg => ?_⟩
      have he : e = fun _ => e () := funext fun u => by cases u; rfl
      rw [he] at hg
      simpa [Fintype.prod_unique] using hform (e ()) g hg

end GroundTheory.Heights₂.Heights
