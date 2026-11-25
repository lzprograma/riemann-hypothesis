module

public import Formalism.FrobeniusOrbits.Statement
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs

@[expose] public section

open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

def DiscrMaximalRealCyclotomic : Prop :=
  ∀ (e : ℕ) (L : Type) [Field L] [NumberField L] (ζ : L), IsPrimitiveRoot ζ (2 ^ (e + 2)) →
    discr (F1 ζ) = 2 ^ (2 ^ e * (e + 1) - 1)

def HostDiscr : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    discr (hostE ζ a b) = 2 ^ (2 ^ (e + 2) * (e + 1) - 4) * ((q * d : ℕ) : ℤ) ^ (2 ^ (e + 1)) ∧
    discr (hostF ζ a b) = 2 ^ (2 ^ (e + 1) * (e + 1) - 2) * ((q * d : ℕ) : ℤ) ^ (2 ^ e) ∧
    discr (hostE ζ a b) = discr (hostF ζ a b) ^ 2 ∧
    (|(discr (hostE ζ a b) : ℝ)| ^ ((1 : ℝ) / (2 ^ (e + 2) : ℝ)) =
      (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d)) ∧
    (|(discr (hostF ζ a b) : ℝ)| ^ ((1 : ℝ) / (2 ^ (e + 1) : ℝ)) =
      (2 : ℝ) ^ ((e : ℝ) + 1 - (2 : ℝ) ^ (-(e : ℝ))) * Real.sqrt ((q : ℝ) * d))

def chC (e : ℕ) : GG e →* ℂˣ := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp (chD e)


open scoped Classical in
open Classical in
def HostCharSum : Prop :=
  ∀ e : ℕ,
    (∀ χ : GG e →* ℂˣ,
      (∑ g ∈ Finset.univ.filter (fun g : GG e => g ∉ Psi e), starRingEnd ℂ ((χ g : ℂˣ) : ℂ)) =
        if χ = 1 then (2 ^ (e + 1) : ℂ) else if χ = chC e then -(2 ^ (e + 1) : ℂ) else 0) ∧
    ∀ g : GG e,
      4 * (if g.1 = ((1 : ℤˣ), (-1 : ℤˣ)) then (1 : ℤ) else 0) =
        (1 - ((chD e g : ℤˣ) : ℤ)) * (1 + ((chQ e g : ℤˣ) : ℤ))

end Formalism.FrobeniusOrbits
