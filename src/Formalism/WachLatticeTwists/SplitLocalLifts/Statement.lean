module

public import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic.TypeStar
import Formalism.CoboundaryTransfers.Statement
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Statement
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.CoboundaryTransfers Formalism.RepresentationBoundsCohomology.N2

def LiftO {O : Type*} [CommRing O] (ℓ : ℕ) {H₁ H₂ : Type*} [AddCommGroup H₁] [Module O H₁]
    [AddCommGroup H₂] [Module O H₂] (Hf₁ : Submodule O H₁) (Hf₂ : Submodule O H₂)
    (g : H₁ →ₗ[O] H₂) (e : ℕ) : Prop :=
  ∀ κ ∈ Hf₂, ((ℓ : O) ^ e) • κ ∈ Hf₁.map g

end Formalism.RepresentationBoundsCohomology.JL
