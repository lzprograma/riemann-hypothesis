module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TowU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsRat {α β κ : Type} [Fintype κ] {B : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F} (d : Darboux B κ) : Prop :=
  ∀ x : Matrix α β E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

variable (σ : E →ₐ[F] E)

variable {σ}


end GlobalTheory.TowU

end
