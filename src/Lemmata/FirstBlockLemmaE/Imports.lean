module

public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace Bl.FirstBlockLemmaE

theorem goal1 {L : Type} [Field L] [NumberField L] :
  (x : L) → (c : ℤ) → x^2 = x + c →
  ∃ (X : NumberField.RingOfIntegers L), X = x ∧ X^2 = X + c := by
  intro x c h
  have hi : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ 2 - (Polynomial.X + Polynomial.C c), ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, h]
      simp
  refine ⟨⟨x, hi⟩, rfl, ?_⟩
  apply NumberField.RingOfIntegers.coe_injective
  exact h

end Bl.FirstBlockLemmaE
