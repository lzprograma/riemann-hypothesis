module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitOnZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitOffZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitGoodPoints
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongMassNearSmall
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarIntAdd
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimit
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.TypeStar
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.MvPolynomial

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOnZero

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOnZero =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOnZero", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitOnZero\npublic import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitOffZero\npublic import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongLimitGoodPoints\npublic import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLelongMassNearSmall\npublic import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarIntAdd\npublic import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimit\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Algebra.MvPolynomial\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff

theorem lelongLimit_off_small (hOff : LelongLimitOffZero.Statement) (hAdd : VarIntAdd.Statement)
    {n d : ℕ} {J I : Ideal (MvPolynomial (Fin n) ℂ)} {u : Fin n → ℂ} {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ))
    (hu : linForm u ∉ J) (hφ : ∀ i, SmoothNear (zeroSet J) (φ i))
    (hloc : ∀ q ∈ zeroSet J, linEval u q = 0 → q ∉ zeroSet I →
      ∃ N ∈ 𝓝 q, ∀ f : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        Tendsto (fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ)) (𝓝[>] 0)
          (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
              (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
            (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d f φ)))
    (g : (Fin n → ℂ) → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hgI : Disjoint (tsupport g) (zeroSet I)) :
    Tendsto (fun ε => varInt J (d + 1) g (vecCons (logReg u ε) φ)) (𝓝[>] 0)
      (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ))
          (_ : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes),
        (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ)) :=
  lelongLimit_of_local_on_tsupport hOff hAdd hJ hdim hu hφ g hg hgc fun q hq hq1 hq2 =>
    hloc q hq1 hq2 (Set.disjoint_left.1 hgI hq)

theorem LelongLimitOnZero.proof (hOff : LelongLimitOffZero.Statement)
    (hGood : LelongLimitGoodPoints.Statement) (hSmall : LelongMassNearSmall.Statement)
    (hAdd : VarIntAdd.Statement) : LelongLimitOnZero.Statement := by
  classical
  intro n d J u φ p hJ hdim hu hφ _ _
  refine ⟨Set.univ, Filter.univ_mem, fun f hf hfc _ => ?_⟩
  obtain ⟨I, hI, hIdim, hloc⟩ := hGood n d J u φ hJ hdim hu hφ
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨χ, hχ, ⟨U, hU, hIU, hχ1⟩, hTχ, hLχ⟩ :=
    hSmall n d J I u φ f hJ hdim hu hφ hI hIdim hf hfc (δ / 3) (by positivity)
  have hχf : ContDiff ℝ ∞ (fun x => χ x * f x) := hχ.mul hf
  have hχfc : HasCompactSupport (fun x => χ x * f x) := hfc.mul_left
  have hg : ContDiff ℝ ∞ (fun x => (1 - χ x) * f x) := (contDiff_const.sub hχ).mul hf
  have hgc : HasCompactSupport (fun x => (1 - χ x) * f x) := hfc.mul_left
  have hgI : Disjoint (tsupport fun x => (1 - χ x) * f x) (zeroSet I) := by
    refine Disjoint.mono_right hIU (Disjoint.closure_left ?_ hU)
    refine Set.disjoint_left.2 fun x hx hxU => hx ?_
    simp [hχ1 x hxU]
  have hsum : (fun x => χ x * f x) + (fun x => (1 - χ x) * f x) = f := by
    funext x
    simp only [Pi.add_apply]
    ring
  obtain ⟨hTadd, hLadd⟩ := lelongSides_add hAdd (u := u) hJ hφ _ _ hχf hχfc hg hgc
  rw [hsum] at hTadd hLadd
  refine ((Metric.tendsto_nhds.1
    (lelongLimit_off_small hOff hAdd hJ hdim hu hφ hloc _ hg hgc hgI) (δ / 3) (by positivity)).and
    (hTχ.and hTadd)).mono fun ε ⟨h1, h2, h3⟩ => ?_
  rw [Real.dist_eq] at h1 ⊢
  rw [h3, hLadd]
  rw [abs_lt] at h1 ⊢
  rw [abs_le] at h2 hLχ
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hLχ.1, hLχ.2]

end GroundTheory.Heights₂.Heights
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimitOnZero =====
