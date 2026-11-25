module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

section Abstract

variable {k Γ I : Type} [Field k] [Group Γ] {a c : ℕ}

abbrev mat (ρ : Γ →* GL (Fin a) k) (g : Γ) : Matrix (Fin a) (Fin a) k := ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)

def word (ρ : Γ →* GL (Fin a) k) (L : List (Γ × k)) : Matrix (Fin a) (Fin a) k :=
  (L.map fun p => mat ρ p.1 - p.2 • (1 : Matrix (Fin a) (Fin a) k)).prod

def Kills (ρ : Γ →* GL (Fin a) k) (j : I → Γ) (χ : I → k) (ω : Fin c → I → k) : Prop :=
  ∀ (σ : Fin c → I) (s : I), word ρ (List.ofFn (fun b => (j (σ b), ω b (σ b))) ++ [(j s, χ s)]) = 0

def TrSum (ρ : Γ →* GL (Fin a) k) (j : I → Γ) (κ : Fin a → I → k) : Prop :=
  ∀ s, trc ρ (j s) = ∑ i, κ i s

end Abstract

end UpperTheory.Gal.NearKilling
