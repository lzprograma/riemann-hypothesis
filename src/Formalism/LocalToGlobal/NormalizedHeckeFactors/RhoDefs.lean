module

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual NumberField IsDedekindDomain Polynomial

namespace Formalism.L2.NR

def IsConjRep {Γ K : Type} [Group Γ] [CommRing K] {n : ℕ} (ρ₁ ρ₂ : Γ →* GL (Fin n) K) : Prop :=
  ∃ P : GL (Fin n) K, ∀ g, ρ₁ g = P * ρ₂ g * P⁻¹

theorem one_le_r (D : D7) : 1 ≤ D.R.r := by
  have := D.R.two_le_m
  show 1 ≤ D.R.k + D.R.m - 1
  omega

end Formalism.L2.NR
