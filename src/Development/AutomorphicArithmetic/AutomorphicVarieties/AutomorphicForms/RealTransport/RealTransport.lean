module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V.Af.Bc

namespace UpperTheory.V.Af.Cr

def IneRes : Prop :=
  ∀ (F₀ F Ω : Type) [Field F₀] [NumberField F₀] [Field F] [NumberField F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω] [Algebra F Ω]
    [IsScalarTower F₀ F Ω] [IsAlgClosure F Ω], ∀ᶠ v : HeightOneSpectrum (𝓞 F₀) in Filter.cofinite,
      ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := F₀) A ≤ (res F₀ Ω F).range

def SSRes : Prop :=
  ∀ (Γ Γ' k : Type) [Group Γ] [Group Γ'] [Field k] (n : ℕ) (r : Γ →* GL (Fin n) k) (φ : Γ' →* Γ), φ.range.Normal →
    IsSSRep r → IsSSRep (r.comp φ)

def RealTransport : Prop :=
  ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K],
    Module.finrank F K = 2 → ∀ χ : HChar F, ∃ χ' : HChar (maximalRealSubfield K),
      (∀ v' : InfinitePlace (maximalRealSubfield K), ∃ v : InfinitePlace F, χ'.locInf v' (-1) = χ.locInf v (-1)) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), normV (w.under (𝓞 (maximalRealSubfield K))) = normV (w.under (𝓞 F)) ∧
        (χ.UnrAt (w.under (𝓞 F)) → χ'.UnrAt (w.under (𝓞 (maximalRealSubfield K))) ∧
          χ'.val (w.under (𝓞 (maximalRealSubfield K))) = χ.val (w.under (𝓞 F)))

def Parallel : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (a : (F →+* ℂ) → ℤ), IsAlgPos χ a →
    ∀ φ φ', a φ = a φ'

def AlgOfSign : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (χ : HChar F) (b : ℤ), IsAlgPos χ (fun _ => b) →
    (∀ v : InfinitePlace F, χ.locInf v (-1) = (-1) ^ b) → χ.IsAlg fun _ => b

def BcDual : Prop :=
  GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual →
  ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field K] [NumberField K] [IsCMField K] [Algebra F K],
    Module.finrank F K = 2 → ∀ (n : ℕ), 1 ≤ n → ∀ (π : TR.CuspSub F n) (χ : HChar F) (P : CuspSub K n), π.Polarized χ → IsBC π P →
    ∃ χ' : HChar (maximalRealSubfield K), (∀ v v' : InfinitePlace (maximalRealSubfield K), χ'.locInf v (-1) = χ'.locInf v' (-1)) ∧
      GlobalTheory.ContraPair.DualIsConjBy P (compNorm K χ')

end UpperTheory.V.Af.Cr
