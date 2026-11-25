module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsQuotientOfIrreducibleUnitarySegmentPr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProductsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
  GlobalTheory.CuspRep GlobalTheory.DefiniteBC

namespace GlobalTheory.SpehRec

theorem isL_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {𝔪 : Multiset (Segment k)} {π : Representation ℂ (GL (Fin N) k) V} {π' : Representation ℂ (GL (Fin N) k) W}
    (h : IsL 𝔪 π) (e : π.Equiv π') : IsL 𝔪 π' := by
  obtain ⟨m, x, hd, hx, hc⟩ := h
  exact ⟨m, x, hd, hx, hc.of_equiv e (.refl _)⟩

section Sum

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem sumList_append (l l' : List (WD h)) : sumList (l ++ l') = (sumList l).lpSum (sumList l') := by
  induction l with
  | nil => simp [sumList, WD.lpSum_comm (WD.lpZero (h := h)), WD.lpSum_zero]
  | cons x l ih =>
    simp only [List.cons_append, sumList, List.foldr_cons] at ih ⊢
    rw [ih, WD.lpSum_assoc]

theorem sumList_flatMap {α : Type*} (L : List α) (f : α → List (WD h)) :
    sumList (L.flatMap f) = sumList (L.map fun i => sumList (f i)) := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.flatMap_cons, sumList_append, ih]
    rfl

end Sum

end GlobalTheory.SpehRec

end
