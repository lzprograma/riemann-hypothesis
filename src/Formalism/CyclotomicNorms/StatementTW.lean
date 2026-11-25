module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.TypeStar

@[expose] public section

open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

def vl {L : Type*} [NormedField L] (ℓ : ℕ) (x : L) : ℝ := -Real.logb ℓ ‖x‖

end Formalism.CyclotomicNorms
