module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates

open scoped InnerProductSpace

def RieszOnRangeStatement (E H : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] : Prop :=
  ∀ (θ : E →ₗ[ℂ] H) (ℓ : E →ₗ[ℂ] ℂ) (A : ℝ), 0 ≤ A →
    (∀ e : E, ‖ℓ e‖ ^ 2 ≤ A * ‖θ e‖ ^ 2) →
    ∃ u ∈ (LinearMap.range θ).topologicalClosure, ‖u‖ ^ 2 ≤ A ∧ ∀ e : E, ⟪u, θ e⟫_ℂ = ℓ e

def OntoWithBoundStatement (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] : Prop :=
  ∀ (G : H₁ →ₗ[ℂ] H₂) (Gs : H₂ →ₗ[ℂ] H₁) (θ : E →ₗ[ℂ] H₁) (Q : Submodule ℂ H₂) (c : ℝ), 0 < c →
    (∀ u ∈ Q, ∀ x : H₁, ⟪Gs u, x⟫_ℂ = ⟪u, G x⟫_ℂ) →
    (∀ u ∈ Q, ∀ e : E, c * ‖u‖ ^ 2 ≤ ‖Gs u + θ e‖ ^ 2) →
    ∀ f ∈ Q, ∃ h : H₁, (∀ u ∈ Q, ⟪u, G h⟫_ℂ = ⟪u, f⟫_ℂ) ∧ (∀ e : E, ⟪h, θ e⟫_ℂ = 0) ∧
      c * ‖h‖ ^ 2 ≤ ‖f‖ ^ 2

end ReciprocityTheory.L2DbarEstimates
