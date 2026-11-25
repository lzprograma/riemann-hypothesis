module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.LieHt

section Lat

variable {K : Type} [Field K] [NumberField K] {m : ℕ}

variable (K' : Type) [Field K'] [NumberField K'] [Algebra K K']


end Lat

structure SemiFib (K : Type) [Field K] [NumberField K] : Type 1 where

  P₀ : Out.PolAV (Sp K)

  G : Over (Sp (𝓞 K))
  [grp : GrpObj G]
  semi : IsSemiAbelian G

  φ : P₀.A.left ⟶ G.left
  fib : IsGrpPullback P₀.A G (spMap (algebraMap (𝓞 K) K)) φ

  v : Fin P₀.g → (epsR K ⟶ P₀.A)
  basis : IsLieBasis v

attribute [instance] SemiFib.grp

namespace SemiFib

variable {K : Type} [Field K] [NumberField K] (F : SemiFib K)

def IsUnif (s : K →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (W : Fin F.P₀.g → Fin g → ℂ) : Prop :=
  ∃ (Q : Out.PolAV (Sp ℂ)) (_ : Q.g = g) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A))
    (u : HolUnif Q.A Q.L g) (χ : u.Λ → ℂ),
    IsPolFibre s F.P₀ Q ψ ∧ u.Λ = Λ ∧ u.IsAH Hm χ ∧ ∀ i, IsVecOver s ψ (F.v i) (v' i) ∧ u.IsDiff (W i) (v' i)

def IsHerm (h : HermFam K (Fin F.P₀.g → K)) : Prop :=
  ∀ s : K →+* ℂ, ∃ (Λ : Submodule ℤ (Fin F.P₀.g → ℂ)) (Hm : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ)
    (W : Fin F.P₀.g → Fin F.P₀.g → ℂ), F.IsUnif s Λ Hm W ∧
      ∀ i j, h.form s (Pi.single i 1) (Pi.single j 1) = Real.pi * hermForm Hm (W j) (W i)

end SemiFib

end GlobalTheory.LieHt
end
