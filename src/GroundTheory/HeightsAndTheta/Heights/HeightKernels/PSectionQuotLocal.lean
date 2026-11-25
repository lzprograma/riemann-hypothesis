module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionQuotFinite
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveSectionQuotLocal
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

theorem SectionQuotLocal.proof : SectionQuotLocal.Statement := by
  intro T _ K' _ _ y s hy hs hsP m t hm hrat a b hb hba
  have hx0 : aeval y s ≠ 0 := SectionQuotientFinite.aeval_ne_zero y hs hsP
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hba
    rcases mul_eq_zero.mp hba with h | h
    · have hb0 : b = 0 := by exact_mod_cast h
      exact hb (hb0 ▸ m.zero_mem)
    · exact hx0 h
  exact Targets.CurveSectionQuotLocal.proof Unit (fun _ => T) K' y s (fun _ => 1) hy hs hsP m
    (fun _ => t) hm (fun _ => hyt) (fun p => hrat p.2) a b hb (by simpa [Fintype.prod_unique] using hba)

end

end GroundTheory.Heights₂.Heights
