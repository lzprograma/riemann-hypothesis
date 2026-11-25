module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralBumpProfOnePos
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.CauchyIntegral
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloContDiffStatement
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Algebra.Order.Star.Real
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.RegBall
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Order.CompletePartialOrder

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralMollProfBall, ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MollifyEqConvolution

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralMollProfBall =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralMollProfBall", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralBumpProfOnePos\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Analysis.Calculus.DiffContOnCl\npublic import Mathlib.Analysis.Complex.CauchyIntegral\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem moll_eq_zero_of_lt {n : ℕ} {t : ℝ} (ht : 0 < t) {z : V n} (hz : t / 2 < ‖z‖) :
    moll n t z = 0 := by
  have h1 : 1 - 4 * (‖z‖ / t) ^ 2 ≤ 0 := by
    have h2 : 1 / 2 < ‖z‖ / t := by
      rw [lt_div_iff₀ ht]; linarith
    nlinarith
  simp only [moll, mollProf, bumpProf, Real.smoothTransition.zero_of_nonpos h1, mul_zero]

theorem holo_eq_mollify {n : ℕ} {f : V n → ℂ} {x : V n} {t : ℝ} (ht : 0 < t)
    (hf : DifferentiableOn ℂ f (closedBall x t)) : mollify n t f x = f x :=
  moll_mean ht (hf.mono ball_subset_closedBall)

end ReciprocityTheory.L2DbarEstimates.C
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralMollProfBall =====

-- ===== clump member: ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MollifyEqConvolution =====
-- clump-header: {"m": "ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MollifyEqConvolution", "h": "module\n\npublic import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloContDiffStatement\npublic import Mathlib.Analysis.Convolution\npublic import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralBumpProfOnePos\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\npublic import Mathlib.Analysis.Calculus.ContDiff.Convolution\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.Order.CompletePartialOrder\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.IntegralMollProfBall\n\n"}
section -- clump:auto
@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal ContDiff Convolution

theorem mollify_eq_convolution (n : ℕ) (t : ℝ) (u : V n → ℂ) :
    mollify n t u = (moll n t) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u := by
  funext x
  rw [convolution_eq_swap]
  simp only [mollify, ContinuousLinearMap.lsmul_apply, Complex.real_smul]

theorem holoSmooth : HoloSmoothStatement := by
  intro n Ω f hΩ hf x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  set r := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hsub : closedBall x₀ (3 * r) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  set g := (closedBall x₀ (3 * r)).indicator f with hg
  have hgi : Integrable g := by
    rw [hg, integrable_indicator_iff measurableSet_closedBall]
    exact (hf.continuousOn.mono hsub).integrableOn_compact (isCompact_closedBall x₀ (3 * r))
  have hconv : ContDiff ℝ ∞ (mollify n r g) := by
    rw [mollify_eq_convolution]
    exact (moll_hasCompactSupport n hr0).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (moll_contDiff n r) hgi.locallyIntegrable
  have heq : f =ᶠ[𝓝 x₀] mollify n r g := by
    filter_upwards [Metric.ball_mem_nhds x₀ hr0] with x hx
    rw [Metric.mem_ball] at hx
    have hx' : closedBall x r ⊆ Ω := by
      refine (Metric.closedBall_subset_closedBall' ?_).trans hsub
      linarith
    rw [← holo_eq_mollify hr0 (hf.mono hx')]
    simp only [mollify]
    congr 1
    funext y
    by_cases hy : y ∈ closedBall x₀ (3 * r)
    · simp [hg, Set.indicator_of_mem hy]
    · have h1 : r / 2 < ‖x - y‖ := by
        rw [Metric.mem_closedBall, not_le] at hy
        have h2 := dist_triangle y x x₀
        have h3 : dist y x = ‖x - y‖ := by rw [dist_comm, dist_eq_norm]
        linarith
      simp [hg, moll_eq_zero_of_lt hr0 h1]
  exact hconv.contDiffAt.congr_of_eventuallyEq heq

theorem holo_contDiffOn {n : ℕ} {Ω : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hΩ : IsOpen Ω) (hf : DifferentiableOn ℂ f Ω) :
    ContDiffOn ℝ ∞ f Ω := by
  exact holoSmooth n Ω f hΩ hf

end ReciprocityTheory.L2DbarEstimates.C
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MollifyEqConvolution =====
