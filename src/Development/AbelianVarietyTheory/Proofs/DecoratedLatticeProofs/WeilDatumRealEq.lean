module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsStdIsVacVec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeLeRealSymplecticPairingSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct

namespace GlobalTheory.RealEqWeil

theorem weilDatum_realEq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om om' : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om' → (∀ τ, ∃ e : ℚ, HasInfExp D χS τ e ∧ HasInfExp D χS' τ e) → (∀ τ, ∃ e : ℚ, HasInfExp D χT τ e ∧ HasInfExp D χT' τ e) → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ f, IsThetaFunO ψ S T f → om (a, b) f = om' (a, b) f := by
  intro D ψ S T χS χT χS' χT' om om' hW hW' hS hT a ha b hb f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D

  have eS : ∀ τ, HasInfExp D (χS' * χS⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hS τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  have eT : ∀ τ, HasInfExp D (χT' * χT⁻¹) τ ((0 : ℤ) : ℚ) := fun τ => by
    obtain ⟨e, h1, h2⟩ := hT τ
    simpa using GlobalTheory.Chain.hasInfExp_div h2 h1
  obtain ⟨om'', hW'', hmv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hW.std S T χS χT (χS' * χS⁻¹) (χT' * χT⁻¹) om hW
    (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecS hW.hecS) (GlobalTheory.WeilVacChar.hecke_mul_inv hW'.hecT hW.hecT)
    (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resS hW.resS) (GlobalTheory.WeilVacChar.resEta_mul_inv hW'.resT hW.resT)
  rw [GlobalTheory.WeilVacChar.mul_mul_inv_cancel, GlobalTheory.WeilVacChar.mul_mul_inv_cancel] at hW''
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ S (GlobalTheory.RealPairBound.gramAt_det_ne D S) a ha
  obtain ⟨y, hy, hyv⟩ := GlobalTheory.OneMapRef.RealMove.exists_root hθ T (GlobalTheory.RealPairBound.gramAt_det_ne D T) b hb
  have x1 : (χT' * χT⁻¹) x = 1 := by
    apply Circle.coe_injective
    rw [hxv _ (fun _ => 0) eT]
    simp
  have y1 : (χS' * χS⁻¹) y = 1 := by
    apply Circle.coe_injective
    rw [hyv _ (fun _ => 0) eS]
    simp
  have h1 := hmv a b x y hx hy
  rw [x1, y1, inv_one, one_mul, Circle.coe_one, one_smul] at h1
  rw [← h1]
  exact GlobalTheory.WeilUniq.weilDatum_unique D ψ hW.std S T χS' χT' om'' om' hW'' hW' (a, b) f hf

end GlobalTheory.RealEqWeil
