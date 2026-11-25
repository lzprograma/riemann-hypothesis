module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf
import Mathlib.Algebra.Module.Torsion.Prod
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Development.WeilBound.ThetaLifts.FrameEstimates.ContinuousMixedSymm

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.StdCharWeilDatum

section Char

variable {F : Type} [Field F] [NumberField F]

theorem at_pairA (x : Ainf F) : At (evI F) (pairA F x 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  show (u.1 * x, u.2 * 0) = ((0 : Ainf F), (0 : Af F))
  rw [h1, zero_mul, mul_zero]

theorem psi_pairA {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : Ainf F) :
    ψ (pairA F x 0) = Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ)) :=
  hψ.2.2 _ (at_pairA x)

theorem norm_psi_inf {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : Ainf F) : ‖ψ (pairA F x 0)‖ = 1 := by
  rw [psi_pairA hψ]; exact PositivityTheory.ThKEst.W.norm_exp_real _

theorem norm_psi_fin {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (y : Af F) : ‖ψ (pairA F 0 y)‖ = 1 := by
  apply _root_.PositivityTheory.ThKEst.W.norm_psi_fin <;> assumption

theorem norm_psi {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : AF F) : ‖ψ x‖ = 1 := by
  rw [PositivityTheory.ThKEst.W.pairA_split x, AddChar.map_add_eq_mul, norm_mul, norm_psi_inf hψ, norm_psi_fin hψ, one_mul]

theorem exists_ne_one {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : ∃ x, ψ x ≠ 1 := by
  apply _root_.PositivityTheory.ThKEst.W.exists_ne_one <;> assumption

theorem isCharAF {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) : IsCharAF F ψ :=
  ⟨hψ.1, norm_psi hψ, hψ.2.1, exists_ne_one hψ⟩

end Char

section Trace

variable {F : Type} [Field F] [NumberField F]

theorem sum_eq_trace (x : Ainf F) :
    ∑ v : InfinitePlace F, (v.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding v (x v)).re =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [Algebra.trace_complex_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2,
      Complex.ofReal_re]
    simp
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun w => ?_
    have h := InfinitePlace.mult_isComplex ⟨w.1, InfinitePlace.not_isReal_iff_isComplex.1 w.2⟩
    simp only at h
    rw [h]
    push_cast
    rfl

end Trace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sum_infFam [IsTotallyReal F] (B : Base F E) (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ))
    (hθ : Formalism.IndefR.DatumF.IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ) (x : Ainf F) :
    ∑ w, θ w (x ⊗ₜ[F] (1 : E)) =
      ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) := by
  rw [← sum_eq_trace]
  push_cast
  refine Fintype.sum_congr _ _ fun w => ?_
  have hv : w.IsReal := IsTotallyReal.isReal w
  rw [GlobalTheory.DualPairCompare.gen_inf_val (B.emb w).1 w (B.emb w).2.symm (θ w) (hθ w) x,
    InfinitePlace.mult_isReal ⟨_, hv⟩, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv,
    Complex.ofReal_re]
  simp

end GlobalTheory.StdCharWeilDatum

end
