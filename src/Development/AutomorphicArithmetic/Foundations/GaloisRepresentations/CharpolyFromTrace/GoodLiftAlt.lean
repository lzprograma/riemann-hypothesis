module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.LimitEig
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.HasTypeVecIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.NumberField

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

def GoodLift : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ) [Fact l.Prime],
    1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ w : HeightOneSpectrum (𝓞 E),
    ∃ (X : UnramifiedFromSplittingCriterion.Fld E Ω) (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
      InertialTypesAlt.Lifts (InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : InertialTypesAlt.Pt E Ω a) ∧ InScope .good l P χ' ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ g ∈ Dec (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g) ∧
        ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → IsSplitAt w') ∧
      ∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))

def AllLift : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ) [Fact l.Prime],
    1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ →
    ∀ S : Set (HeightOneSpectrum (𝓞 E)), (∀ u ∉ S, ∃ B, (CG.mk π).HasSat u B) → ∀ X : UnramifiedFromSplittingCriterion.Fld E Ω, UnramifiedFromSplittingCriterion.Tower S X →
    ∃ (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
      InertialTypesAlt.Lifts (InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : InertialTypesAlt.Pt E Ω a) ∧ InScope .all l P χ' ∧
      ∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))

end UpperTheory.Gal.NearKilling
