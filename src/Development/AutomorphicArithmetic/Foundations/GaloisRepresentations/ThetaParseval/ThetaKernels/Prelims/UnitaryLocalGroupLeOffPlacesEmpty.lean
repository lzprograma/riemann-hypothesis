module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcCompFinAwayPtOfNotMem
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExtensionEmbeddingEvInfRealAd
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.ThetaLifts.LatticeBasics.EulerA
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

section
/-! # BlockScaledIntegralOfLocal: Preliminary helper declarations for global theta kernels. -/

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKTorus.IntegralOfAdic

theorem evFin_realAd (F : Type) [Field F] [NumberField F] (v : Pl F) (x : ℝ) :
    evFin F v (realAd F x) = 0 := by
  show evalV F v 0 = 0
  exact map_zero _

end GlobalTheory.ThKTorus.IntegralOfAdic
end
end

/-! # UnitaryLocalGroupLeOffPlacesEmpty: Preliminary helper declarations for global theta kernels. -/

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

private theorem evInf_realAd_one {F : Type} [Field F] [NumberField F] (w : InfinitePlace F) :
    evInf F w (realAd F 1) = 1 := by
  apply (InfinitePlace.Completion.extensionEmbedding w).injective
  rw [GlobalTheory.CompanionTheory.RealAdeleComponent.extensionEmbedding_evInf_realAd, map_one]
  simp

theorem UpperTheory.unitaryLocalGroup_le_offPlaces_empty :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {X : Spc F E n} (v : Pl (F := F)), locGrp σ X v ≤ gOff σ X ∅ := by
  intro F E _ _ _ _ _ σ n X v
  refine (Subgroup.closure_le _).2 fun g hg => Subgroup.subset_closure ⟨fun w => ?_, by simp⟩
  have h0 : realAd F 1 • (mat g - 1) = 0 := hg _ (GlobalTheory.ThKTorus.IntegralOfAdic.evFin_realAd F v 1)
  ext i j
  have e := congrArg (fun M : Matrix (Fin n) (Fin n) (AE F E) => compInf F E w (M i j)) h0
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, map_zero] at e
  rw [GlobalTheory.AwayFix.Chart.compInf_smul_away, evInf_realAd_one, one_smul, map_sub, sub_eq_zero] at e
  rw [Matrix.map_apply, e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp
