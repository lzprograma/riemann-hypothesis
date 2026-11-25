module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

namespace PositivityTheory.Lbc

def torusChar {k : Type} [Field k] {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ))
    (t : ∀ _ : Fin n, GL (Fin 1) k) : ℂ :=
  ∏ a, ((ξ a (Matrix.GeneralLinearGroup.det (t a)) : ℂˣ) : ℂ)

end PositivityTheory.Lbc

end
