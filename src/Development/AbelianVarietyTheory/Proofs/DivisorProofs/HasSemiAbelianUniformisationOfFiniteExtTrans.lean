module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegComp

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_generic_lift {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {i : R →+* R'}
    (hi : Function.Injective i) {D : DegPre R} {D' : DegPre R'} (p : IsPullDeg i D D') :
    ∃ s : (TK R).left ⟶ p.W.toScheme, s ≫ p.W.ι = jK R := by
  have H : Set.range (jK R).base ⊆ Set.range p.W.ι.base := by
    rintro _ ⟨y, rfl⟩
    let z' : (TK R').left := (default : PrimeSpectrum (FractionRing R'))
    have e₁ : (genMap hi).base z' = y := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    have e₂ : (jK R' ≫ spMap i).base z' = (genMap hi ≫ jK R).base z' := by
      rw [← fracMap_sq hi, Category.id_comp]
    refine ⟨(p.g).base z', ?_⟩
    rw [← Scheme.Hom.comp_apply, p.g_comm]
    exact e₂.trans (by rw [Scheme.Hom.comp_apply, e₁])
  exact ⟨IsOpenImmersion.lift p.W.ι (jK R) H, IsOpenImmersion.lift_fac _ _ _⟩

theorem nonempty_isPullDeg_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R'']
    [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} (hi : Function.Injective i) (hj : Function.Injective j)
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'') :
    Nonempty (IsPullDeg (j.comp i) D D'') := by
  intros
  apply _root_.GlobalTheory.PullDegCompGen.nonempty_isPullDeg_comp <;> assumption

end GlobalTheory.PullDegComp

namespace GlobalTheory.Mum

theorem hasFin_of_finExt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')),
    Nonempty (IsPullDeg ρ D.toPre D'.toPre) → HasFin D' → HasFin D := by
  intro R R' _ _ _ _ _ _ ρ hρ D D' ⟨p⟩ ⟨R'', _, _, _, σ, D'', hσ, ⟨q⟩, hH⟩
  exact ⟨R'', _, _, _, σ.comp ρ, D'', ⟨hσ.1, hσ.2.1.comp hρ.2.1, hσ.2.2.comp hρ.2.2⟩,
    GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hρ.2.1 hσ.2.1 p q, hH⟩

end GlobalTheory.Mum
