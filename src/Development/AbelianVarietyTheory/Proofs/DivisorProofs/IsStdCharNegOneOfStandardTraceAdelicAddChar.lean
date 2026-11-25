module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
import Mathlib.Algebra.Module.Torsion.Prod
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

namespace GlobalTheory.StdCharFromIsStd

variable {F : Type} [Field F] [NumberField F]

theorem at_pairA (x : Ainf F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (pairA F x 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
  rw [h1, zero_mul, mul_zero]

theorem psi_pairA {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : Ainf F) :
    ψ (pairA F x 0) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ)) :=
  hψ.2.2 _ (at_pairA x)

theorem norm_exp_real (r : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (r : ℂ))‖ = 1 := by
  have : -(2 * Real.pi * Complex.I) * (r : ℂ) = ((-(2 * Real.pi * r) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_psi_inf {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : Ainf F) :
    ‖ψ (pairA F x 0)‖ = 1 := by
  rw [psi_pairA hψ]; exact norm_exp_real _

theorem pairA_split (x : AF F) : x = pairA F x.1 0 + pairA F 0 x.2 := by
  show x = ((x.1 + 0 : Ainf F), (0 + x.2 : Af F))
  rw [add_zero, zero_add]
  rfl

theorem norm_psi_fin {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (y : Af F) :
    ‖ψ (pairA F 0 y)‖ = 1 := by
  have hc : Continuous fun y : Af F => ‖ψ (pairA F 0 y)‖ :=
    (hψ.1.comp (continuous_const.prodMk continuous_id)).norm
  have hcl : IsClosed {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := isClosed_eq hc continuous_const
  have hrange : Set.range (algebraMap F (Af F)) ⊆ {y : Af F | ‖ψ (pairA F 0 y)‖ = 1} := by
    rintro _ ⟨a, rfl⟩
    have h1 := hψ.2.1 a
    rw [GlobalTheory.AdeleCharTwist.algebraMap_eq_pairA, AddChar.map_add_eq_mul] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_psi_inf hψ, one_mul, norm_one] at h2
    exact h2
  have := hcl.closure_subset_iff.2 hrange
  rw [GlobalTheory.AdeleCharTwist.denseRange_fin.closure_range] at this
  exact this (Set.mem_univ y)

theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  rw [pairA_split x, AddChar.map_add_eq_mul, norm_mul, norm_psi_inf hψ, norm_psi_fin hψ, one_mul]

theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : ∃ x, ψ x ≠ 1 := by
  set n : ℕ := Module.finrank ℝ (mixedEmbedding.mixedSpace F)
  have hn : 0 < n := Module.finrank_pos
  set t : ℝ := 1 / (2 * n)
  refine ⟨pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t)) 0, ?_⟩
  rw [psi_pairA hψ, RingEquiv.apply_symm_apply, Algebra.trace_algebraMap]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have eR : (n • t : ℝ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    simp only [t]
    rw [mul_one_div, div_eq_div_iff (by positivity) two_ne_zero]
    ring
  have e : ((n • t : ℝ) : ℂ) = 1 / 2 := by
    rw [eR]; push_cast; ring
  rw [e]
  have : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem isCharAF {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) : IsCharAF F ψ :=
  ⟨hψ.1, norm_psi hψ, hψ.2.1, exists_ne_one hψ⟩

end GlobalTheory.StdCharFromIsStd

namespace GlobalTheory.StdCharFromIsStd

theorem isStdChar_of_isStd : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsStdChar D ψ (-1) := by
  intro D ψ hψ
  refine ⟨isCharAF hψ, GlobalTheory.DualPairCompare.exists_infFam D, fun θ hθ x => ?_⟩
  change ψ (pairA D.host.F x 0) = _
  rw [psi_pairA hψ, GlobalTheory.DualPairCompare.sum_infFam θ hθ, GlobalTheory.BaseGoodPlace.trInf_eq_trace]
  congr 1
  push_cast
  ring

end GlobalTheory.StdCharFromIsStd
