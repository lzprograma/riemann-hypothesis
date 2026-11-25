module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.Continuity
import Mathlib.NumberTheory.Height.NumberField

@[expose] public section

namespace Formalism.HermitianLattices.LocalLatticeBases

open Finset Matrix

def LemmaB'_avg : Prop :=
  ∀ (k n : ℕ) (S : Finset (Fin k → ℕ)) (mult : (Fin k → ℕ) → ℕ),
    (∀ σ : Equiv.Perm (Fin k), ∀ w ∈ S, w ∘ σ ∈ S) →
    (∀ σ : Equiv.Perm (Fin k), ∀ w, mult (w ∘ σ) = mult w) →
    (∀ w ∈ S, ∑ i, w i = n) →
    ∀ j : Fin k, k * ∑ w ∈ S, mult w * w j = n * ∑ w ∈ S, mult w

end Formalism.HermitianLattices.LocalLatticeBases
