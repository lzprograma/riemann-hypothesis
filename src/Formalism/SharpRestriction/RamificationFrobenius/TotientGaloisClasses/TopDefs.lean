module

public import Formalism.SharpRestriction.FamCore
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.HC

def EAt (Λ : Level) (D : D7) (x eps C : ℝ) : Prop := EAtH Λ D.host.toHostRaw D.host.TT x eps C

def EFamC (Λ : Level) {eps : ℝ} (Fm : FamCore eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, EAt Λ (Fm.D x i) x eps C

end Formalism.HC

end
