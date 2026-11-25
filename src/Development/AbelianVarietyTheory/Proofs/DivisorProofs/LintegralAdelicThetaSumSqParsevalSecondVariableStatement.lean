module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)


theorem _root_.GlobalTheory.T.lintegral_adelicThetaSum_sq_parseval_second_variable : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (𝓕₁ : Set (κ → AF F)), @IsAddFundamentalDomain (GlobalTheory.ThetaParseval.ratVec F κ) _ _ _ (borel _) 𝓕₁ μ → μ 𝓕₁ ≠ ⊤ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ x : (κ → AF F),
      ∫⁻ y in 𝓕₁, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, y) Φ)‖ₑ ^ 2 ∂μ =
        μ 𝓕₁ * ∑' ξ : κ → F, ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ₑ ^ 2 := by
  first | exact @GlobalTheory.ThetaParsevalInner.lintegral_thetaSum_schr_sq
