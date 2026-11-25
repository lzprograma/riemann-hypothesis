module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorThetaFunSupModerateGrowth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
open GlobalTheory.Asc

namespace GlobalTheory.SupThetaGrowth

theorem om_sup_quotHeight : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h w, ‖om (g, h) f w‖ ≤ C * (quotHeight S g * quotHeight T h) ^ A := by
  intro D ψ S T χS χT om hom f hf
  obtain ⟨C, A, hC⟩ := om_sup_growth D ψ S T χS χT om hom f hf
  refine ⟨max C 0 * 4 ^ A, A, fun g h w => ?_⟩
  obtain ⟨γ, hγ, h1⟩ := exists_height_le_two_mul_quotHeight S g
  obtain ⟨γ', hγ', h2⟩ := exists_height_le_two_mul_quotHeight T h
  have e := om_rat_mul D ψ S T χS χT om hom f hf γ⁻¹ (inv_mem hγ) γ'⁻¹ (inv_mem hγ') (γ * g) (γ' * h) w
  rw [inv_mul_cancel_left, inv_mul_cancel_left] at e
  rw [e]
  have p1 := (height_pos S (γ * g)).le
  have p2 := (height_pos T (γ' * h)).le
  have q1 := (quotHeight_pos S g).le
  calc _ ≤ C * (height S (γ * g) * height T (γ' * h)) ^ A := hC _ _ _
    _ ≤ max C 0 * (height S (γ * g) * height T (γ' * h)) ^ A :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (mul_nonneg p1 p2) A)
    _ ≤ max C 0 * (2 * quotHeight S g * (2 * quotHeight T h)) ^ A :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg p1 p2)
          (mul_le_mul h1 h2 p2 (mul_nonneg zero_le_two q1)) A) (le_max_right _ _)
    _ = max C 0 * 4 ^ A * (quotHeight S g * quotHeight T h) ^ A := by
        generalize quotHeight S g = a
        generalize quotHeight T h = b
        rw [show 2 * a * (2 * b) = 4 * (a * b) by ring, mul_pow, mul_assoc]

end GlobalTheory.SupThetaGrowth
