module

import Development.WeilBound.CoreStatements.FlagImmersions.CombLineSmoothConjInvariant
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem combLine_smooth_conj :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ((∀ j, IsSmoothHerm (ℓ j)) → IsSmoothHerm (combLine ℓ n)) ∧ ((∀ j, IsConjInvariantH (ℓ j)) → IsConjInvariantH (combLine ℓ n)) ∧ IsSmoothHerm (trivLine ι) := by
  apply RootFieldNumerics.combLine_smooth_conj_invariant

end GlobalTheory.CompanionTheory.Ar.Top
