module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
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

@[expose] public section

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.WeilL2Words.StdArch

theorem supportedAtArchimedean_adeleOfMixedSpaceComponent (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (GlobalTheory.WeilL2Words.arch1 F z) := by
  intro u hu
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · exact mul_zero u.2

theorem evI_arch1 (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (GlobalTheory.WeilL2Words.arch1 F z) = z :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply z

theorem isStdInf_of_isStd : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → GlobalTheory.WeilL2Words.IsStdInf F ψ := by
  intro F _ _ ψ hψ
  refine ⟨-(Algebra.trace ℝ (mixedEmbedding.mixedSpace F)), fun z hz => ?_, fun z => ?_⟩
  · by_contra! h
    exact hz (GlobalTheory.ArchUniq.Coord.eq_zero_of_trace z fun b => by
      have := h b
      rw [LinearMap.neg_apply, neg_eq_zero] at this
      exact this)
  · rw [hψ.2.2 _ (supportedAtArchimedean_adeleOfMixedSpaceComponent F z), evI_arch1]
    simp only [LinearMap.neg_apply, Complex.ofReal_neg]
    ring_nf

end GlobalTheory.WeilL2Words.StdArch

end
