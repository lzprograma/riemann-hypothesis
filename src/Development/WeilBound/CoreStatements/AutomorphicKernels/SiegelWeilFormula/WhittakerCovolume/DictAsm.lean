module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.SectionLinearFinsetSum

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

set_option linter.unusedSectionVars false

theorem asm_incl (e : E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) e = HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) e := rfl

theorem asm_cA (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ z := rfl

theorem asm_half : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [show (2 : AF F) = algebraMap F (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul]
  norm_num

theorem asm_scalar_mul {n : ℕ} (η : E) (M : Matrix (Fin n) (Fin n) (AE F E)) :
    incM F (Matrix.scalar (Fin n) η) * M = (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) η) • M := by
  ext i j
  simp only [incM, Matrix.mul_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, apply_ite,
    map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.smul_apply, smul_eq_mul]
  rfl

theorem asm_cpow_split {C ν : ℝ} (hC : 0 < C) (hν : 0 < ν) (w : ℂ) :
    ((C * ν⁻¹ : ℝ) : ℂ) ^ w = (C : ℂ) ^ w * (ν : ℂ) ^ (-w) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hC.le (inv_nonneg.2 hν.le), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hν.le]; exact Real.pi_pos.ne), Complex.cpow_neg]

theorem asm_meanC_smul {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (μH : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ J))
    (𝓕 : Set (HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ J)) (c : ℂ) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
    (S : Set (Fin n → Fin M → E)) :
    HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ M J (fun Y => c * Φ Y) S) =
      c * HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ M J Φ S) := by
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.meanC, HeckeCharacterZeroLocus.SiegelWeilU.thetaS, tsum_mul_left, integral_const_mul, Complex.real_smul]
  ring

end PositivityTheory.SiegelWeilFormula.KWhit

end
