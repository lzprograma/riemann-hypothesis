module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

open WeightedAtlas

def INDCountStatement : Prop :=
  ∀ n j : ℕ, (multiLe n j).card = (j + n).choose n

def tube (f : ℕ) (Ω : Set (Fin f → ℝ)) : Set (Fin f → ℂ) :=
  {s | (fun k => (s k).im) ∈ Ω}

def fourCoeff {f : ℕ} (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ) (ν : Fin f → ℤ) : ℂ :=
  ∫ x in Set.univ.pi (fun _ : Fin f => Set.Ioc (0 : ℝ) 1),
    h (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I) *
      Complex.exp (-2 * Real.pi * Complex.I *
        ∑ k, (ν k : ℂ) * ((x k : ℂ) + (b k : ℂ) * Complex.I))

def FOURIndepStatement (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h : (Fin f → ℂ) → ℂ),
    IsOpen Ω → IsPreconnected Ω → DifferentiableOn ℂ h (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h (s + fun k => (m k : ℂ)) = h s) →
    ∀ b ∈ Ω, ∀ b' ∈ Ω, ∀ ν, fourCoeff h b ν = fourCoeff h b' ν

def FOURBoundStatement (f : ℕ) : Prop :=
  ∀ (h : (Fin f → ℂ) → ℂ) (b : Fin f → ℝ) (ν : Fin f → ℤ) (C : ℝ),
    (∀ x : Fin f → ℝ, ‖h (fun k => (x k : ℂ) + (b k : ℂ) * Complex.I)‖ ≤ C) →
    ‖fourCoeff h b ν‖ * Real.exp (-2 * Real.pi * ∑ k, (ν k : ℝ) * b k) ≤ C

def FOURSignStatement (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h : (Fin f → ℂ) → ℂ) (b0 κ : Fin f → ℝ) (C E : ℝ),
    IsOpen Ω → IsPreconnected Ω → DifferentiableOn ℂ h (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h (s + fun k => (m k : ℂ)) = h s) →
    (∀ t : ℝ, 0 ≤ t → b0 + t • κ ∈ Ω) →
    (∀ t : ℝ, 0 ≤ t → ∀ x : Fin f → ℝ,
      ‖h (fun k => (x k : ℂ) + ((b0 + t • κ) k : ℂ) * Complex.I)‖ ≤ C * (1 + t) ^ E) →
    ∀ ν : Fin f → ℤ, fourCoeff h b0 ν ≠ 0 → 0 ≤ ∑ k, (ν k : ℝ) * κ k

def FOURSumStatement (f : ℕ) : Prop :=
  ∀ (Ω : Set (Fin f → ℝ)) (h : (Fin f → ℂ) → ℂ),
    IsOpen Ω → DifferentiableOn ℂ h (tube f Ω) →
    (∀ s ∈ tube f Ω, ∀ m : Fin f → ℤ, h (s + fun k => (m k : ℂ)) = h s) → (0 : Fin f → ℝ) ∈ Ω →
    Summable (fun ν : Fin f → ℤ => ‖fourCoeff h 0 ν‖) →
    ∀ x : Fin f → ℝ, HasSum (fun ν : Fin f → ℤ => fourCoeff h 0 ν *
      Complex.exp (2 * Real.pi * Complex.I * ∑ k, (ν k : ℂ) * (x k : ℂ))) (h (fun k => (x k : ℂ)))

end

end ReciprocityTheory.L2DbarEstimates.Y
