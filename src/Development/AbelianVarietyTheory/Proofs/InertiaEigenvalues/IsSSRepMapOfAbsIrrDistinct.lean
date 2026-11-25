module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

noncomputable section

namespace GlobalTheory.ConstituentsCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

open Polynomial Formalism.ConjugateSelfDual

def BrauerNesbitt : Prop :=
  ∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' → (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly = ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) → ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹

end GlobalTheory.ConstituentsCompare

end
