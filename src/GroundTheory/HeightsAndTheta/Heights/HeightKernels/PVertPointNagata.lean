module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointNagata
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingPow
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointMultChart
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveVertPointNagata
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

theorem VertPointNagata.proof (hCh : VertPointChart.Statement) : VertPointNagata.Statement := by
  intro T _ K' _ _ y s hP hs hsP W hW t ht _ _ a b hb hab
  obtain ⟨Φ₀, hsurj₀, hker₀, hΦ₀⟩ := Targets.CurveVertPointNagata.of_single hP hs hsP hW
    (fun _ => t) (fun _ => ht) (fun p => a p.2) (fun p => b p.2) (fun p => hb p.2)
    (fun p => hab p.2) (fun e g hg => by
      simpa using (hCh T K' y s hP hs hsP W hW t ht).2.2 (e ()) g (by
        have he : (fun _ : Unit => e ()) = e := funext fun u => by cases u; rfl
        rwa [he]))
  let η := mNagataUnitEquiv (Localization.AtPrime (curvePtIdeal y W))
  refine ⟨η.toRingHom.comp Φ₀, η.surjective.comp hsurj₀, ?_, fun f => ?_⟩
  · ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff η.toRingHom η.injective,
      ← RingHom.mem_ker, hker₀]
  · rw [RingHom.comp_apply, hΦ₀ f]
    change mNagataUnitEquiv _ (algebraMap _ _ _) = _
    rw [mNagataUnitEquiv_algebraMap]
    congr 1
    have hm : ∀ q, mvPolyUnitEquiv (Localization.AtPrime (curvePtIdeal y W)) q =
        MvPolynomial.eval₂Hom Polynomial.C (fun _ : Unit => Polynomial.X) q := fun _ => rfl
    induction f using MvPolynomial.induction_on with
    | C n =>
      rw [aeval_C, aeval_C]
      exact RingHom.congr_fun (RingHom.ext_int
        ((mvPolyUnitEquiv _).toRingHom.comp (algebraMap ℤ _)) (algebraMap ℤ _)) n
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      rcases i with ⟨⟨⟩, u⟩
      rw [map_mul, map_mul, map_mul, hp, aeval_X, aeval_X, hm, map_mul, eval₂Hom_C, eval₂Hom_X']

end

end GroundTheory.Heights₂.Heights
