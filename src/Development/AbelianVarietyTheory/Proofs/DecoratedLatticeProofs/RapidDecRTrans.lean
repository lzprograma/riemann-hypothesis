module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.RTransDecay

theorem rapidDec_rTrans : ∀ (D : D7) (V : HSp D) (G : GA D V → ℂ), RapidDec V G → (∀ h, RapidDec V (rTrans h G)) ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ g h, ‖G (g * h)‖ * quotHeight V g ^ N ≤ C * height V h ^ N := by
  intro D V G hG
  refine ⟨fun h => hG.mul_right h, fun N => ?_⟩
  obtain ⟨C, hC⟩ := hG.decay N
  refine ⟨C, fun g h => ?_⟩
  have h1 : GlobalTheory.Grow.quotHeight V g ≤ GlobalTheory.Grow.quotHeight V (g * h) * GlobalTheory.Grow.height V h := by
    simpa using GlobalTheory.Grow.quotHeight_mul_le V (g * h) h⁻¹
  calc ‖G (g * h)‖ * GlobalTheory.Grow.quotHeight V g ^ N
        ≤ ‖G (g * h)‖ * (GlobalTheory.Grow.quotHeight V (g * h) * GlobalTheory.Grow.height V h) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (GlobalTheory.Grow.quotHeight_pos V g).le h1 N) (norm_nonneg _)
    _ = ‖G (g * h)‖ * GlobalTheory.Grow.quotHeight V (g * h) ^ N * GlobalTheory.Grow.height V h ^ N := by ring
    _ ≤ C * GlobalTheory.Grow.height V h ^ N := mul_le_mul_of_nonneg_right (hC _) (pow_pos (GlobalTheory.Grow.height_pos V h) N).le

end GlobalTheory.RTransDecay
