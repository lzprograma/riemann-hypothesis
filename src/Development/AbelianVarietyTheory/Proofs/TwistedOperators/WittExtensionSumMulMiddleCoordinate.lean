module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.BumpMix

variable {D : D7}

theorem witt_extension_sum_mul_middle_coordinate {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    (d.extY T a + d.extX T x + d.ext0 T w₀) * d.j0 = w₀ := by
  simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_j0,
    HypDec.pY_j0, HypDec.p0_j0, Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero]

theorem coord_jX {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    (d.extY T a + d.extX T x + d.ext0 T w₀) * d.jX = x := by
  simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jX,
    HypDec.pY_jX, HypDec.p0_jX, Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero]

theorem coord_jY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    (d.extY T a + d.extX T x + d.ext0 T w₀) * d.jY = a := by
  simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc, HypDec.pX_jY,
    HypDec.pY_jY, HypDec.p0_jY, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem eq_coords {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (u : WO S T) :
    u = d.extX T (u * d.jX) + d.ext0 T (u * d.j0) + d.extY T (u * d.jY) :=
  ((d.coordS T).symm_apply_apply u).symm

theorem symplOH_Y_X {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x a : Mx D T.rank ρ) :
    symplOH S T (d.extY T a) (d.extX T x) = -trHalf D (pairS T x a) := by
  rw [symplOH_skew, d.symplOH_extX_extY]

def poinX (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (β : Mx D T.rank ρ → ℂ) (u : WO S T) : ℂ :=
  ∑' γ : Matrix (Fin T.rank) (Fin ρ) D.host.E,
    ψ (trHalf D (pairS T (u * d.jX + 2 • rat γ) (u * d.jY))) * β (u * d.jX + rat γ)

theorem poinX_coords (ψ : AddChar (AF D.host.F) ℂ) {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (β : Mx D T.rank ρ → ℂ) (x a : Mx D T.rank ρ) (w₀ : WO S₀ T) :
    poinX ψ d T β (d.extY T a + d.extX T x + d.ext0 T w₀) =
      ∑' γ : Matrix (Fin T.rank) (Fin ρ) D.host.E, ψ (trHalf D (pairS T (x + 2 • rat γ) a)) * β (x + rat γ) := by
  simp only [poinX, coord_jX, coord_jY]

end GlobalTheory.BumpMix

end
