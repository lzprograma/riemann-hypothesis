module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw

def P_contr_id : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (_ : IsUnifAt ϖ) (n : ℕ) (y : Fin n → ℤ)
    (_ : StrictAnti y) (δ : GLw n w) (_ : dcos n w (tdiag ϖ y) δ ≠ 0),
    ∃ m ∈ iwGL n w, ∃ τ ∈ TO n w, m⁻¹ * δ * m = tdiag ϖ y * τ

def P_contr_tw : Prop := ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (_ : Unr E) (w : Pl E) (_ : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (_ : IsUnifAt ϖ) (n : ℕ)
    (y : Fin n → ℤ) (_ : StrictAnti y) (δ : GLw n w) (_ : dcos n w (tdiag ϖ y) δ ≠ 0),
    ∃ m ∈ iwGL n w, ∃ τ ∈ TO n w, m⁻¹ * δ * thL n w m = tdiag ϖ y * τ

end PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
