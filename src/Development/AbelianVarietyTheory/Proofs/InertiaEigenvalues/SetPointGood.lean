module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.SetPtOff

theorem litBurnside_all (D : D7) : LitBurnside (G D.host.E D.nd.Om) := by
  intro l _ a ρ h
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    exact Subsingleton.elim _ _
  · apply GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub ρ
    refine ⟨?_, ?_, ?_⟩
    · intro hb
      have : (Pi.single (⟨0, ha⟩ : Fin a) (1 : CyclotomicNorms.Fbar l) : Fin a → CyclotomicNorms.Fbar l) ∈ (⊤ : Submodule (CyclotomicNorms.Fbar l) (Fin a → CyclotomicNorms.Fbar l)) := trivial
      rw [hb, Submodule.mem_bot] at this
      have h1 := congrFun this ⟨0, ha⟩
      simp at h1
    · intro g x _; trivial
    · intro W' _ hW'
      exact h W' (fun g _ x hx => hW' g x hx)

end GlobalTheory.SetPtOff
