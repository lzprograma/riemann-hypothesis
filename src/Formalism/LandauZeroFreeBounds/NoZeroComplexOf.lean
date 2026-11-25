module

public import Formalism.LandauZeroFreeBounds.Statement
public import Formalism.ZeroFreeRegion.Statement

@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def negLD {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)

def LGrowth : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
    ‖DirichletCharacter.LFunction χ s‖ ≤ C * q * (1 + ‖s‖)

def LInvBound : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 1 < s.re →
    ‖DirichletCharacter.LFunction χ s‖⁻¹ ≤ s.re / (s.re - 1)

def LLogDerivRight : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 1 < s.re →
    ‖negLD χ s‖ ≤ 1 / (s.re - 1) + C

def Positivity : Prop :=
  ∀ (q : ℕ) [NeZero q] (σ : ℝ), 1 < σ →
    (∀ (χ : DirichletCharacter ℂ q) (t : ℝ),
      0 ≤ 3 * (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re + 4 * (negLD χ ((σ : ℂ) + t * I)).re
        + (negLD (χ ^ 2) ((σ : ℂ) + 2 * t * I)).re) ∧
    (∀ χ : DirichletCharacter ℂ q, χ ^ 2 = 1 →
      0 ≤ (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re + (negLD χ (σ : ℂ)).re) ∧
    (∀ χ₁ χ₂ : DirichletCharacter ℂ q, χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 →
      0 ≤ (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re + (negLD χ₁ (σ : ℂ)).re
        + (negLD χ₂ (σ : ℂ)).re + (negLD (χ₁ * χ₂) (σ : ℂ)).re)

def RealConj : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 → ∀ s : ℂ,
    DirichletCharacter.LFunction χ (starRingEnd ℂ s) = starRingEnd ℂ (DirichletCharacter.LFunction χ s)

def LocalZeros : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ,
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔
        (ρ ∈ Metric.closedBall ((11 / 10 : ℂ) + t * I) (1 / 5) ∧ DirichletCharacter.LFunction χ ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ = 0 → 2 ≤ m ρ) ∧
      ∀ σ : ℝ, 1 < σ → σ ≤ 6 / 5 →
        (negLD χ ((σ : ℂ) + t * I)).re ≤
          C * Real.log ((q : ℝ) * (|t| + 2)) - ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + t * I - ρ)).re

def NoZeroComplex : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    χ ^ 2 ≠ 1 → InRegion c q s → DirichletCharacter.LFunction χ s ≠ 0

def NoZeroComplexOf : Prop := LocalZeros → LLogDerivRight → Positivity → NoZeroComplex

end Formalism.ZeroFreeDirichlet
