module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs

@[expose] public section

noncomputable section

namespace SiegelEisensteinSeries

open Filter Topology

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def WHolo (D : Set (E →ₗ[ℂ] ℂ)) (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∀ ν ∈ D, DifferentiableOn ℂ (fun s => ν (f s)) U

variable {I : Type*}

end SiegelEisensteinSeries
