module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic.TypeStar
public import Mathlib.Analysis.InnerProductSpace.Defs

@[expose] public section

open Filter Topology
open scoped ContDiff

noncomputable section

namespace SmoothVectors

open scoped Matrix.Norms.Elementwise

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsClosedMatrixGroup (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop :=
  IsClosed G ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ G ∧ (∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) ∧
    ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1

def lieAlg (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ G}

end SmoothVectors

end
