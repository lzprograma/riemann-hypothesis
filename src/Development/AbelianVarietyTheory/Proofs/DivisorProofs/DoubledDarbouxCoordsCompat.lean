module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.StandardTraceAdelicAddCharLocalComponentNeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowSplit

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

namespace GlobalTheory.DiagNonvan

open scoped Classical
open GlobalTheory.DiagForm GlobalTheory.StdCharFromIsStd

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem eq_zero_of_psi_mul {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (b : AF F) (h : ∀ y : AF F, ψ (b * y) = 1) :
    b = 0 := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have h1 : b.1 = 0 := by
    refine e.injective ?_
    rw [map_zero]
    refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun s => ?_
    by_contra hT
    set T := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (e b.1 * s) with hTdef
    have h2 := h (pairA F (e.symm ((1 / (2 * T)) • s)) 0)
    have e1 : b * pairA F (e.symm ((1 / (2 * T)) • s)) 0 = pairA F (b.1 * e.symm ((1 / (2 * T)) • s)) 0 := by
      show ((b.1 * _, b.2 * 0) : Ainf F × Af F) = (_, 0)
      rw [mul_zero]
      rfl
    have e2 : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (e (b.1 * e.symm ((1 / (2 * T)) • s))) = 1 / 2 := by
      rw [map_mul, RingEquiv.apply_symm_apply, mul_smul_comm, map_smul, ← hTdef, smul_eq_mul]
      field_simp
    rw [e1, psi_pairA hψ] at h2
    change Complex.exp (_ * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (e (b.1 * e.symm ((1 / (2 * T)) • s))) : ℝ) : ℂ)) = 1 at h2
    have e3 : -(2 * (Real.pi : ℂ) * Complex.I) * ((1 / 2 : ℝ) : ℂ) = -(Real.pi * Complex.I) := by push_cast; ring
    rw [e2, e3, Complex.exp_neg, Complex.exp_pi_mul_I] at h2
    norm_num at h2
  have h2 : b.2 = 0 := by
    refine af_ext fun v => ?_
    rw [map_zero]
    by_contra hv
    apply Tw.PsiNontriv.psiV_ne_one ψ hψ v
    ext t
    rw [GlobalTheory.VacAny.psiV_apply, AddChar.one_apply, ← h (pairA F 0 (singleFin v ((evalV F v b.2)⁻¹ * t)))]
    congr 1
    show ((0, singleFin v t) : Ainf F × Af F) = (b.1 * 0, b.2 * singleFin v ((evalV F v b.2)⁻¹ * t))
    rw [mul_zero]
    congr 1
    refine af_ext fun u => ?_
    by_cases hu : u = v
    · subst hu
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    · rw [map_mul, evalV_singleFin_ne hu, evalV_singleFin_ne hu, mul_zero]
  exact Prod.ext h1 h2

theorem continuous_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  first
  | exact _root_.PositivityTheory.ThKF0.Split.continuous_ofMixed
  | (apply _root_.PositivityTheory.ThKF0.Split.continuous_ofMixed <;> assumption)

theorem continuous_glue : Continuous (glue : Vi F κ × Vf F κ → κ → AdeleRing (𝓞 F) F) :=
  continuous_pi fun i =>
    (continuous_symm.comp ((continuous_apply i).comp ((eI F κ).continuous.comp continuous_fst))).prodMk
      ((continuous_apply i).comp continuous_snd)

theorem glue_add (p q : Vi F κ × Vf F κ) : glue (p + q) = glue p + glue q := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ (p.1 + q.1) i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i) +
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ q.1 i)
  rw [map_add (f := _), Pi.add_apply, map_add (f := _)]

theorem glue_zero : glue (0 : Vi F κ × Vf F κ) = 0 := by
  have h := glue_add (0 : Vi F κ × Vf F κ) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

instance mu_haar : (mu F κ).IsAddHaarMeasure := by unfold mu; infer_instance

end GlobalTheory.DiagNonvan

end
