module

public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DiscreteSeries

theorem isDS_sk_imp_upqRep (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsDS ε lam σ → PI.UpqRep.IsDS ε lam σ :=
  fun h => h

end GlobalTheory.CompanionTheory.DiscreteSeries
