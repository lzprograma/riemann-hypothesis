module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupActionFourierBesselBasePoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFullRankBesselBasePoint
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointIsUnfoldingBasePointSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittDecompositionProjectionZeroMulEEqZero, Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselGroupActsBasePointUnitriangular, Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpec, Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpecStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittDecompositionProjectionZeroMulEEqZero =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittDecompositionProjectionZeroMulEEqZero", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.FBL

variable {D : D7} {σ : ℕ}

def toCore (B : BesL D σ) : FB.BesCore D σ :=
  ⟨B.V, B.V₀, B.A, B.L, B.d, B.o, B.ζ, B.line⟩

def x0Mat (B : BesL D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E := FB.x0MatCore (toCore B)

theorem rat_x0Mat (B : BesL D σ) : rat (x0Mat B) = xLast B.d (vecB B.o B.ζ) := FB.rat_x0MatCore (toCore B)

def besselBasePointLevelNorm (B : BesL D σ) : D.host.E := FB.normCore (toCore B)

theorem besselBasePointLevelNorm_eq_gram_form (B : BesL D σ) : besselBasePointLevelNorm B = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ :=
  FB.normCore_eq (toCore B)

theorem besselBasePointLevelNorm_ne_zero (B : BesL D σ) : besselBasePointLevelNorm B ≠ 0 :=
  FB.normCore_ne_zero (toCore B)

def besselBasePointLeftInverse (B : BesL D σ) : Matrix (Fin (σ + 1)) (Fin B.V.rank) D.host.E := FB.leftInvCore (toCore B)

theorem besselLevelDatum_qX_dot_e_eq_one (B : BesL D σ) : B.d.qX * B.d.e = 1 := FB.qX_e_core (toCore B)

theorem wittDecomposition_projectionX_mul_anisotropicInclusion_eq_zero (B : BesL D σ) : B.d.qX * B.d.i₀ = 0 := FB.qX_i0_core (toCore B)

theorem wittDecomposition_projectionZero_mul_e_eq_zero (B : BesL D σ) : B.d.q0 * B.d.e = 0 := FB.q0_e_core (toCore B)

theorem wittDecomposition_projectionZero_mul_anisotropicInclusion_eq_one (B : BesL D σ) : B.d.q0 * B.d.i₀ = 1 := FB.q0_i0_core (toCore B)

theorem besselBasePointLeftInverse_mul_snocMatrix (B : BesL D σ) : besselBasePointLeftInverse B * x0Mat B = 1 :=
  FB.leftInvCore_mul (toCore B)

theorem xLast_rat_leftInv : ∀ (D : D7) (σ : ℕ) (B : BesL D σ),
    (∃ P ∈ ratMx D (σ + 1) B.V.rank, P ⬝ xLast B.d (vecB B.o B.ζ) = 1) ∧ xLast B.d (vecB B.o B.ζ) ∈ ratMx D B.V.rank (σ + 1) :=
  fun _ _ B => FB.xLast_rat_leftInv_core (toCore B)

end GlobalTheory.Asc.FBL
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittDecompositionProjectionZeroMulEEqZero =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselGroupActsBasePointUnitriangular =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselGroupActsBasePointUnitriangular", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupActionFourierBesselBasePoint\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittDecompositionProjectionZeroMulEEqZero\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
open GlobalTheory.Asc

namespace GlobalTheory.Asc.FBL

variable {D : D7} {σ : ℕ}

def actUni (B : BesL D σ) : Subgroup (GA D B.V) := FB.actUniCore (toCore B)

theorem mem_actUni_iff (B : BesL D σ) (g : GA D B.V) : g ∈ actUni B ↔ ∃ u ∈ UX D σ, ∃ v : Fin σ → AE D,
    mt B.V g ⬝ B.d.jX = B.d.jX ⬝ u.1 ∧
      mt B.V g *ᵥ (B.d.j0 *ᵥ ratV (vecB B.o B.ζ)) = B.d.j0 *ᵥ ratV (vecB B.o B.ζ) + B.d.jX *ᵥ v :=
  FB.mem_actUniCore_iff (toCore B) g

theorem flagN_le_actUni (B : BesL D σ) : flagN B.d ≤ actUni B := FB.flagN_le_actUniCore (toCore B)

theorem embA_mem_actUni (B : BesL D σ) (h : GA D B.A) : embA B.d B.o h ∈ actUni B := FB.embA_mem_actUniCore (toCore B) h

theorem besGrp_le_actUni (B : BesL D σ) : besGrp B.d B.o ≤ actUni B := FB.besGrp_le_actUniCore (toCore B)

theorem mem_besGrp_of_actUni (B : BesL D σ) (g : GA D B.V) (hg : g ∈ actUni B) : g ∈ besGrp B.d B.o :=
  FB.mem_besGrp_of_actUniCore (toCore B) g hg

theorem besGrp_act_xLast : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), (∀ g : GA D B.V, g ∈ besGrp B.d B.o ↔ ∃ u ∈ UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1) ∧ (∀ a a' : Mx D (σ + 1) (σ + 1), xLast B.d (vecB B.o B.ζ) ⬝ a = xLast B.d (vecB B.o B.ζ) ⬝ a' → a = a') ∧ ∀ g ∈ GQ B.V, ∀ u : UX D (σ + 1), mt B.V g ⬝ xLast B.d (vecB B.o B.ζ) = xLast B.d (vecB B.o B.ζ) ⬝ u.1.1 → u ∈ UXQ D (σ + 1) :=
  fun _ _ B => FB.besGrp_act_xLast_core (toCore B)

end GlobalTheory.Asc.FBL

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselGroupActsBasePointUnitriangular =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpec =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpec", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselBasePointIsUnfoldingBasePointSpec\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselGroupActsBasePointUnitriangular\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalFullRankBesselBasePoint\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
open GlobalTheory.Asc

namespace GlobalTheory.Asc.FBL

variable {D : D7} {σ : ℕ}

def zlQ (B : BesL D σ) : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E := vecMulVec B.ζ (GlobalTheory.Unf.FB.eLast D (σ + 1))

theorem rat_zlQ (B : BesL D σ) : (rat (zlQ B) : Mx D B.L.rank (σ + 1)) = zEll B.L (σ + 1) B.ζ := by
  rw [zEll, ← GlobalTheory.Unf.FB.ratV_eLast]
  funext i j
  simp [rat, zlQ, vecMulVec_apply, ratV]

theorem gramQ_zlQ_mulVec_last (B : BesL D σ) (a : Fin (σ + 1) → D.host.E) :
    (gramQ B.L (zlQ B) *ᵥ a) (Fin.last σ) = (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ) * a (Fin.last σ) := by
  simp only [gramQ, zlQ, Matrix.mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, vecMulVec_apply,
    GlobalTheory.Unf.FB.eLast, Pi.star_apply, Fin.val_last]
  simp only [ite_true, mul_one]
  rw [Finset.sum_eq_single (Fin.last σ)]
  · simp only [Fin.val_last, ite_true, mul_one]
  · intro b _ hb
    have hb' : ¬ (b.1 + 1 = σ + 1) := fun h => hb (Fin.ext (by simp only [Fin.val_last]; omega))
    simp only [hb', ite_false, mul_zero, Finset.sum_const_zero, zero_mul]
  · simp

theorem basePoint_spec : ∀ (D : D7) (σ : ℕ) (B : BesL D σ), ∃ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) ∧ IsBase B.V x₀ ∧ Rgrp B.V (rat x₀ : Mx D B.V.rank (σ + 1)) = besGrp B.d B.o ∧ (∀ a : Fin (σ + 1) → D.host.E, gramQ B.V x₀ *ᵥ a = 0 → a (Fin.last σ) = 0) ∧ ∀ (S S₀ : HSp D) (d : HypDec S S₀ (σ + 1)) (c : skewA D (σ + 1)), d.qS B.V c (xLast B.d (vecB B.o B.ζ)) = d.qS B.L c (zEll B.L (σ + 1) B.ζ) := by
  intro D σ B
  obtain ⟨x, ⟨hli, hg⟩, hx⟩ := _root_.GlobalTheory.Asc.FBx.exists_rat_eq_xLast D σ B
  rw [← rat_zlQ] at hg
  have hG : gramQ B.V x = gramQ B.L (zlQ B) := GlobalTheory.Unf.FB.gramQ_eq_of_gramSkew x (zlQ B) hg
  have hA : adj (xLast B.d (vecB B.o B.ζ)) ⬝ (gA B.V ⬝ xLast B.d (vecB B.o B.ζ)) =
      adj (zEll B.L (σ + 1) B.ζ) ⬝ (gA B.L ⬝ zEll B.L (σ + 1) B.ζ) := by
    rw [← hx, ← rat_zlQ, ← GlobalTheory.Unf.FB.rat_gramQ, ← GlobalTheory.Unf.FB.rat_gramQ, hG]
  refine ⟨x, hx, ⟨hli, fun u hu => ?_⟩, ?_, fun a ha => ?_, fun S S₀ d c => ?_⟩
  · rw [GlobalTheory.Unf.FB.rat_gramQ, hx, hA]
    have hz : zEll B.L (σ + 1) B.ζ ⬝ u.1 = zEll B.L (σ + 1) B.ζ := zEll_mul B.L B.ζ hu
    calc adj u.1 ⬝ (adj (zEll B.L (σ + 1) B.ζ) ⬝ (gA B.L ⬝ zEll B.L (σ + 1) B.ζ) ⬝ u.1)
          = adj (zEll B.L (σ + 1) B.ζ ⬝ u.1) ⬝ (gA B.L ⬝ (zEll B.L (σ + 1) B.ζ ⬝ u.1)) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = adj (zEll B.L (σ + 1) B.ζ) ⬝ (gA B.L ⬝ zEll B.L (σ + 1) B.ζ) := by rw [hz]
  · ext g
    rw [hx]
    exact ((_root_.GlobalTheory.Asc.FBL.besGrp_act_xLast D σ B).1 g).symm
  · have h1 := congrFun ha (Fin.last σ)
    rw [hG, gramQ_zlQ_mulVec_last, Pi.zero_apply] at h1
    exact (mul_eq_zero.1 h1).resolve_left B.line.2
  · rw [HypDec.qS, HypDec.qS, HypDec.symplOH_extX_extY, HypDec.symplOH_extX_extY, GlobalTheory.Unf.FB.pairS_mul,
      GlobalTheory.Unf.FB.pairS_mul, hA]

end GlobalTheory.Asc.FBL
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpec =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpecStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpecStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpec\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
open GlobalTheory.Asc

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselBasePointIsUnfoldingBasePointSpecStatement =====
