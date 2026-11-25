module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

def SdEx : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J →
  ∀ ψ : AddChar (AF F) ℂ, HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F ψ → ∀ n : ℕ,
    (∃ μ, HeckeCharacterZeroLocus.SiegelWeilU.SdW F E σ M J (AF F) ψ n μ) ∧ ∃ ν, HeckeCharacterZeroLocus.SiegelWeilU.SdHerm F E σ (AF F) ψ n ν

end PositivityTheory.SiegelWeilFormula.KWhit

end
