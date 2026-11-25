module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Height.NumberField

@[expose] public section

open Finset NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

def PrimeLogSum : Prop :=
  ∀ (Y : ℝ), 1 ≤ Y → ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y + Real.log 4

end Formalism.DivisionValues
