module

public import Mathlib.Analysis.Normed.Ring.Ultra
public import Formalism.EllipticTorsion.Statement
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Polynomial
public import Formalism.EllipticTorsion.IsoExpand
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Data.Finset.Max
public import Formalism.EllipticTorsion.EllipticTorsionProofs.LegendreInvariant
public import Formalism.EllipticTorsion.UnitCancel
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero
public import Formalism.FormalGroupLog.FormalGroupLogProofs.HomPsSubstMvSubst
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsParamDef
public import Formalism.EllipticTorsion.EllipticTorsionProofs.WPoint
public import Formalism.EllipticTorsion.CoeffRing
public import Formalism.EllipticTorsion.FormalGroupPointsParametrisation
public import Formalism.EllipticTorsion.EllipticTorsionProofs.CubeTwo
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsSubgroupHolds
public import Formalism.EllipticTorsion.EllipticTorsionProofs.TorInt
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.EllipticTorsion.EllipticTorsionProofs.CubeThree
import Formalism.EllipticTorsion.EllipticTorsionProofs.Deuring
import Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsUnitFactor
import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsHomDef
import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsNoPrimeToPTorsion
import Formalism.EllipticTorsion.EllipticTorsionProofs.NDeriv
import Formalism.EllipticTorsion.EllipticTorsionProofs.WSeries
import Formalism.EllipticTorsion.EllipticTorsionProofs.WSubst

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsSumPowPrimePow, Formalism.EllipticTorsion.EllipticTorsionProofs.IsogenyExpansion, Formalism.EllipticTorsion.EllipticTorsionProofs.Legendre, Formalism.EllipticTorsion.EllipticTorsionProofs.ModelUnitOf, Formalism.EllipticTorsion.EllipticTorsionProofs.UnitCancel, Formalism.EllipticTorsion.FormalGroupPointsNoTorsion

-- ===== clump member: Formalism.EllipticTorsion.EllipticTorsionProofs.IsogenyExpansion =====
-- clump-header: {"m": "Formalism.EllipticTorsion.EllipticTorsionProofs.IsogenyExpansion", "h": "module\n\npublic import Formalism.EllipticTorsion.IsoExpand\npublic import Mathlib.GroupTheory.QuotientGroup.Defs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Algebra.BigOperators.Group.Finset.Basic\npublic import Mathlib.Algebra.BigOperators.Group.Finset.Sigma\npublic import Mathlib.Algebra.Group.Submonoid.BigOperators\npublic import Mathlib.Algebra.Module.BigOperators\npublic import Mathlib.Data.Finset.Max\n\n"}
section -- clump:auto
@[expose] public section

open Finset

namespace Formalism.ELL.QuadraticDifferenceHypotheses

universe u

section Exact
variable {O M Q : Type u} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup Q]

structure BiHyp (bar : O → O) (ψ : M → Q) : Prop where
  add1 : ∀ a a' b : M, quadDiff ψ (a + a') b = quadDiff ψ a b + quadDiff ψ a' b
  zero : ψ 0 = 0
  adj : ∀ (α : O) (a b : M), quadDiff ψ (α • a) b = quadDiff ψ a (bar α • b)

end Exact

section Quot
variable {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T]

end Quot

end Formalism.ELL.QuadraticDifferenceHypotheses

namespace Formalism.ELL

open Formalism.ELL.QuadraticDifferenceHypotheses

universe u

end Formalism.ELL
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.EllipticTorsion.EllipticTorsionProofs.IsogenyExpansion =====

-- ===== clump member: Formalism.EllipticTorsion.EllipticTorsionProofs.Legendre =====
-- clump-header: {"m": "Formalism.EllipticTorsion.EllipticTorsionProofs.Legendre", "h": "module\n\npublic import Formalism.EllipticTorsion.Statement\npublic import Formalism.EllipticTorsion.EllipticTorsionProofs.LegendreInvariant\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.ELL

namespace LegendreModelEllipticTorsion

open Polynomial

noncomputable def legPoly {K : Type*} [Field K] (j : K) : K[X] :=
  C 256 * (X ^ 2 - X + 1) ^ 3 - C j * (X * (X - 1)) ^ 2

theorem legPoly_natDegree {K : Type*} [Field K] (h : (256 : K) ≠ 0) (j : K) :
    (legPoly j).natDegree = 6 := by
  unfold legPoly
  compute_degree!

theorem norm_one_add {K : Type*} [NormedField K] [IsUltrametricDist K] {t : K} (ht : ‖t‖ ≠ 1) :
    ‖1 + t‖ = max 1 ‖t‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : K)) (y := t)
    (by rw [norm_one]; exact fun h => ht h.symm)
  simpa using this

end LegendreModelEllipticTorsion

end Formalism.ELL
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.EllipticTorsion.EllipticTorsionProofs.Legendre =====

-- ===== clump member: Formalism.EllipticTorsion.EllipticTorsionProofs.ModelUnitOf =====
-- clump-header: {"m": "Formalism.EllipticTorsion.EllipticTorsionProofs.ModelUnitOf", "h": "module\n\npublic import Formalism.EllipticTorsion.Statement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\npublic import Mathlib.Analysis.Normed.Ring.Ultra\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

universe u

namespace Formalism.ELL.unitAtAlt

open Formalism.ELL

lemma two_or_three {K : Type u} [NormedField K] [IsUltrametricDist K] :
    ‖(2 : K)‖ = 1 ∨ ‖(3 : K)‖ = 1 := by
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 2
  have h3 : ‖(3 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 3
  have h1 : ‖(1 : K)‖ ≤ max ‖(3 : K)‖ ‖(2 : K)‖ := by
    have : (1 : K) = 3 + -2 := by norm_num
    rw [this]
    simpa [norm_neg] using IsUltrametricDist.norm_add_le_max (3 : K) (-2)
  rw [norm_one] at h1
  by_cases h : ‖(2 : K)‖ = 1
  · exact Or.inl h
  · right
    have hlt : ‖(2 : K)‖ < 1 := lt_of_le_of_ne h2 h
    rcases le_max_iff.mp h1 with h' | h'
    · exact le_antisymm h3 h'
    · exact absurd h' (not_le.mpr hlt)

lemma of_model {K : Type u} [NormedField K] (W : WeierstrassCurve K) (j : K)
    (hI : IntegralModel W) (hc : W.c₄ ^ 3 = j * W.Δ) (hΔ : ‖W.Δ‖ = 1) :
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic),
      IntegralModel W ∧ ‖W.Δ‖ = 1 ∧ W.j = j := by
  have hne : W.Δ ≠ 0 := by
    intro h; rw [h, norm_zero] at hΔ; exact zero_ne_one hΔ
  have : W.IsElliptic := ⟨hne.isUnit⟩
  refine ⟨W, inferInstance, hI, hΔ, ?_⟩
  rw [WeierstrassCurve.j, hc, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  field_simp

end Formalism.ELL.unitAtAlt
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.EllipticTorsion.EllipticTorsionProofs.ModelUnitOf =====

-- ===== clump member: Formalism.EllipticTorsion.FormalGroupPointsNoTorsion =====
-- clump-header: {"m": "Formalism.EllipticTorsion.FormalGroupPointsNoTorsion", "h": "module\n\npublic import Formalism.EllipticTorsion.UnitCancel\npublic import Formalism.FormalGroupLog.FormalGroupLogProofs.HomPsSubstMvSubst\npublic import Mathlib.NumberTheory.Padics.RingHoms\npublic import Mathlib.Topology.Algebra.Polynomial\npublic import Formalism.EllipticTorsion.CoeffRing\npublic import Formalism.EllipticTorsion.CompExpWeight\npublic import Formalism.EllipticTorsion.EllipticTorsionWeights\npublic import Formalism.EllipticTorsion.FormalGroupPointsParametrisation\npublic import Formalism.EllipticTorsion.IsoExpand\npublic import Formalism.EllipticTorsion.EllipticTorsionProofs.CoefficientWeightsLemmaTwo\nimport Formalism.EllipticTorsion.EllipticTorsionProofs.CompExp\nimport Formalism.EllipticTorsion.EllipticTorsionProofs.CubeThree\npublic import Formalism.EllipticTorsion.EllipticTorsionProofs.CubeTwo\nimport Formalism.EllipticTorsion.EllipticTorsionProofs.Deuring\npublic import Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsSumPowPrimePow\nimport Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsUnitFactor\nimport Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsHomDef\nimport Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsNoPrimeToPTorsion\npublic import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsParamDef\npublic import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsSubgroupHolds\npublic import Formalism.EllipticTorsion.EllipticTorsionProofs.IntegralPSBserSubOne\npublic import Formalism.EllipticTorsion.EllipticTorsionProofs.IsogenyExpansion\nimport Formalism.EllipticTorsion.EllipticTorsionProofs.Legendre\npublic import Formalism.EllipticTorsion.EllipticTorsionProofs.LegendreInvariant\nimport Formalism.EllipticTorsion.EllipticTorsionProofs.ModelUnitOf\nimport Formalism.EllipticTorsion.EllipticTorsionProofs.NDeriv\npublic import Formalism.EllipticTorsion.EllipticTorsionProofs.TorInt\nimport Formalism.EllipticTorsion.EllipticTorsionProofs.UnitCancel\nimport Formalism.EllipticTorsion.EllipticTorsionProofs.WPoint\nimport Formalism.EllipticTorsion.EllipticTorsionProofs.WSeries\nimport Formalism.EllipticTorsion.EllipticTorsionProofs.WSubst\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

universe u

namespace Formalism.ELL

theorem formal_group_points_subgroup : FormalGroupPointsSubgroup'.{u} := formal_group_points_subgroup_holds
theorem formal_group_points_no_torsion : FormalGroupPointsTorsionFree.{u} := formal_group_points_no_prime_to_p_torsion
theorem torsionIntegral : TorsionIntegral.{u} := torsionIntegral_of formal_group_points_no_torsion



alias wSeriesUnique := _root_.Formalism.ELL.wSeriesExistsUnique_holds
alias wSeriesLead := _root_.Formalism.ELL.wSeriesLeadingTerm_holds
alias wSubstUnique := _root_.Formalism.ELL.wSeriesSubstUnique_holds
theorem wPoint : WPoint.{u} := wSeriesNonsingularPoint_holds
theorem wChordSeries : WChordSeries.{u} := wChordSeries_of wSubstUnique
theorem wChordSubst : WChordSubst.{u} := wChordSubst_of wSeriesSubstUnique_holds
theorem wFormalGroup : WFormalGroup.{u} := by
  apply wFormalGroup_of <;> first | exact wChordSeries | exact wChordSubst | exact wPoint

theorem formal_group_points_param : FormalGroupPointsParametrisation.{u} := _root_.Formalism.ELL.formal_group_points_param_holds

end Formalism.ELL
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.EllipticTorsion.FormalGroupPointsNoTorsion =====
