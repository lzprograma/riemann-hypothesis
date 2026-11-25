module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.SymplecticFormCoordinates
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.IsOpAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtThetaTransformHeisenbergRealLine

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.RatWeilOp

namespace PositivityTheory.SiegelWeilFormula.TBij

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid


open scoped Classical in
theorem comp_schA {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ'] (τ : κ ≃ κ')
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : (fun x : κ' → AF F => Φ (x ∘ τ)) ∈ schA F κ' :=
  _root_.GlobalTheory.ThetaLineDeriv.comp_mem_schA τ hΦ

theorem act_one' {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] (w : (κ → R) × (κ → R)) :
    act (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) R) w = w := by
  simp [act]

theorem jj_mul_jj {R κ : Type} [CommRing R] [Fintype κ] [DecidableEq κ] : jj κ R * jj κ R = -1 := by
  rw [jj, Matrix.fromBlocks_multiply]
  ext (i | i) (j | j) <;> simp [Matrix.one_apply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end PositivityTheory.SiegelWeilFormula.TBij

end
