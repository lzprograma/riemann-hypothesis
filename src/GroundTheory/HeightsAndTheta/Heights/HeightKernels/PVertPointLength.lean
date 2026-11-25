module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
public import GroundTheory.HeightsAndTheta.Heights.Intersections.MultAtPosOfMemDivSupp
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointLength

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

theorem VertPointLength.proof (hCh : VertPointChart.Statement)
    (hInj : VertPointInj.Statement) (hSurj : VertPointSurj.Statement)
    (hMC : VertPointMultChart.Statement) (hSQ : SectionQuotLocal.Statement) :
    VertPointLength.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  exact Targets.CurveVertPointLength.of_single hs
    (fun W hW c hc => by
      obtain ⟨hmax, hrat, hmem⟩ := hCh T K' y s hP hs hsP W hW (c ()) (hc ())
      refine ⟨hmax, fun p => hrat p.2, fun e g hg => ?_⟩
      simpa using hmem (e ()) g (by
        have he : (fun _ : Unit => e ()) = e := funext fun u => by cases u; rfl
        rwa [he]))
    (hInj T K' y s hP hs hsP)
    (fun m hm hne => hSurj T K' y s hP hs hsP m hm hne)
    (fun W hW c hc a b hb hab => hMC T K' y s hP hs hsP W hW (c ()) (hc ()) a b hb (by simpa using hab))
    (fun m c hm _ hrat a b hb hab =>
      hSQ T K' y s hP hs hsP m (c ()) hm (fun u => hrat ⟨(), u⟩) a b hb (by simpa using hab))

end

end GroundTheory.Heights₂.Heights
