module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem ident : IdentStatement := by
  intro n Ω F a hΩ hc hF ha h0 x hx
  let L : ℂ → V n := fun t => a + t • (x - a)
  let U := L ⁻¹' Ω
  have hLd : Differentiable ℂ L := (differentiable_const a).add (differentiable_id.smul_const (x - a))
  suffices h : EqOn (F ∘ L) 0 U by
    simpa [L] using h (show (1 : ℂ) ∈ U by simpa [U, L] using hx)
  refine ((hF.comp hLd.differentiableOn (show MapsTo L U Ω from fun _ ht => ht)).analyticOnNhd
    (hΩ.preimage hLd.continuous)).eqOn_zero_of_preconnected_of_eventuallyEq_zero ?_
      (show (0 : ℂ) ∈ U by simpa [U, L] using ha) ?_
  · suffices h : Convex ℝ U from h.isPreconnected
    intro t ht u hu s r hs hr hsr
    change L (s • t + r • u) ∈ Ω
    rw [show L (s • t + r • u) = s • L t + r • L u by
      calc
        _ = (s + r) • a + (s • t + r • u) • (x - a) := by simp [L, hsr]
        _ = _ := by simp only [L, smul_add, add_smul, smul_assoc]; abel]
    exact hc ht hu hs hr hsr
  · exact (show Tendsto L (𝓝 0) (𝓝 a) by simpa [L] using hLd.continuous.tendsto 0).eventually h0

end ReciprocityTheory.L2DbarEstimates.C
