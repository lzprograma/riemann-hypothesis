module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrdAlt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct


namespace UpperTheory.Gal.projectedFormsSystemPart

open UpperTheory.V.Z.Ord UpperTheory.Zero.LLC

def TypePlain : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub E n) (w : Plc E) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GLw n w)), π.IsLocComp w σ →
    ∀ rc : IrrGL (k := w.adicCompletion E) → WD h, IsRecT h rc → ∀ χ : Fin n → G E Ω →* ℂˣ,
      IsTypeWD h (fun i => (χ i).comp (Ine (F := E) A).subtype) (rc (algNorm σ)) →
      GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

def AwayOk (s : HidaSetting l L Ω) {n : ℕ} (ι : Qbar l ≃+* ℂ) (ρ : G L Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι ρ π ∧
    ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → w.under (𝓞 (Lp L)) ≠ s.v0 → TU π w

end UpperTheory.Gal.projectedFormsSystemPart

end
