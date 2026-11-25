module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.SharedLemmas.PrecompleteFinite

@[expose] public section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finCompl :
    ∀ (Λ M : Type) [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ) [IsAdicComplete I Λ] [AddCommGroup M] [Module Λ M] [Module.Finite Λ M], IsAdicComplete I M := by
  intro Λ M _ _ I _ _ _ _
  exact
    { toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson I)
      toIsPrecomplete := Formalism.SharedLemmas.isPrecomplete_of_moduleFinite I }
