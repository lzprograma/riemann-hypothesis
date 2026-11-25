module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeDeRhamOnModificationOfFlagCover
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris

noncomputable section

namespace GlobalTheory.DeRham

open GlobalTheory.Published GlobalTheory.Published.AbelianDeRham



theorem IsKSValue.exists_of_isAbelianScheme (P : AbelianDeRham) {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]
    {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (epsRed K) i) {g : ℕ} (hA : Semi.IsAbelianScheme A')
    (hg : SmoothOfRelativeDimension g A'.hom) {f : HdR A} (hf : f ∈ Fil A) : ∃ v, IsKSValue h f v := by
  apply _root_.GlobalTheory.DeRham.IsKSValue.exists_of_isAbelianScheme_ring <;> assumption

theorem ksRegular_of_isAbelianScheme : GlobalTheory.Published.AbelianDeRham → ∀ {K : Type} [Field K] {A : Over (Sp K)}
    [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {g : ℕ}, Semi.IsAbelianScheme A' →
    SmoothOfRelativeDimension g A'.hom → KSRegular h := by
  intro P K _ A _ A' _ i h g hA hg f hf
  obtain ⟨v, hv⟩ := IsKSValue.exists_of_isAbelianScheme P h hA hg hf
  exact ⟨v, hv, fun w hw => IsKSValue.unique P hA hg hw hv⟩

end GlobalTheory.DeRham
