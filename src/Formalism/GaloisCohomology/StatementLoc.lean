module

public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.Padics.Complex

@[expose] public section

noncomputable section

open Representation ReciprocityTheory.Gal

namespace Formalism.GaloisCohomology

variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))

abbrev GK : Type := PadicAlgCl l ≃ₐ[K] PadicAlgCl l

def inertiaSet : Set (GK l K) := {σ | ∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}

def inertiaK : Subgroup (GK l K) := Subgroup.closure (inertiaSet l K)

variable {l K}

end Formalism.GaloisCohomology
