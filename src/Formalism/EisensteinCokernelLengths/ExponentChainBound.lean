module

public import Formalism.WindowSums.Statement

@[expose] public section

noncomputable section

namespace Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

open Polynomial

def FirstRelationModule : Prop :=
  ∀ (A : Type) [CommRing A] (ℓ : ℕ) [Fact ℓ.Prime], 3 ≤ ℓ →
    ∀ (X u : A) (M η r : ℕ), 1 ≤ M →
      (ℓ : A) ^ (⌊((M : ℝ) + η) / ((ℓ : ℝ) - 1)⌋₊ + 1) * (u * X * (X + (ℓ : A)) ^ (ℓ - 1)) ^ r ∈
        Ideal.span {(ℓ : A) ^ ⌈(r : ℝ) * ℓ / ((ℓ : ℝ) - 1)⌉₊, X ^ M * (X + (ℓ : A)) ^ η}

def ExponentChainBound : Prop :=
  ∀ (ℓ b b' S E lam σ₂ h'' c' : ℝ), 2 ≤ ℓ → 0 ≤ b → 0 ≤ S → 0 ≤ E → 0 ≤ σ₂ → 0 ≤ lam →
    c' ≤ b' + S - b / ℓ + 2 + lam →
    max 0 ((((b + S) + 1) / (ℓ - 1) + 1 + E + σ₂ + h'' - b') + σ₂ + c' - h'') ≤
      b / (ℓ * (ℓ - 1)) + E + 2 * σ₂ + 2 * S + 5 + lam

end Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria
