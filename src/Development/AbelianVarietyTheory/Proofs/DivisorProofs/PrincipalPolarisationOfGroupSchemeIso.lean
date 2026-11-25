module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarisationOnAbLocusRestrictAffineOpenStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowSt

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj

namespace GlobalTheory.PolOfIso

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}

theorem relAmple_pull_of_affine (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull φ)} (hw : PGen w)
    (hf : ∀ U' : S'.Opens, IsAffineOpen U' → ∃ U : S.Opens, IsAffineOpen U ∧ U' ≤ f ⁻¹ᵁ U) (hA : RelAmple A L) :
    RelAmple A' L' := by
  apply _root_.GlobalTheory.KeyVals.PolOpen.relAmple_pull_of_affine <;> assumption

theorem sym_pull_of_iso [GrpObj A] [GrpObj A'] (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull φ)} (hw : PGen w) (hs : Sym A L) : Sym A' L' := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := hs (f s)
  refine ⟨f ⁻¹ᵁ U, hU, ?_⟩
  have le' : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) ≤ φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := fun y hy =>
    (congrArg (fun q => q y ∈ U) h.1.w).mpr hy
  have hψ : φ.resLE _ _ le' ≫ (A.hom ⁻¹ᵁ U).ι = (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ φ := Scheme.Hom.resLE_comp_ι φ le'
  obtain ⟨t', ht'⟩ := gen_chartPull (chartPullSame L
    (fun k => ![(A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι ≫ (GrpObj.inv : A' ⟶ A').left, (A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U)).ι] k ≫ φ) _ _
    (φ.resLE _ _ le') fun k => by
      fin_cases k
      · show (_ ≫ _) ≫ φ = _ ≫ _ ≫ _
        rw [Category.assoc, PolBaseChange.inv_comm h, ← Category.assoc, ← hψ, Category.assoc]
      · exact hψ.symm) t ht
  exact exists_down hw hL hL' t' ht'

end GlobalTheory.PolOfIso

namespace GlobalTheory

theorem polarisation_of_iso :
    ∀ (S : Scheme.{0}) (P : PolAV S) (B : Over S) [GrpObj B] (e : B ≅ P.A), IsMonHom e.hom → ∀ L : LB B.left, L.IsLB → LBIso L (P.L.pull e.hom.left) → IsProper B.hom ∧ SmoothOfRelativeDimension P.g B.hom ∧ Sym B L ∧ RelAmple B L ∧ KTriv B L := by
  intro S P B _ e he L hL ⟨w, hw⟩
  have h := isGrpPullback_of_iso e
  have hw' := (isGen_iff w).1 hw
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) h.1 P.isAb.proper,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim,
    PolOfIso.sym_pull_of_iso h P.isLB hL hw' P.sym,
    PolOfIso.relAmple_pull_of_affine h.1 P.isLB hL hw' (fun U hU => ⟨U, hU, fun _ hy => hy⟩) P.ample,
    kTriv_pull h P.isLB hL hw' P.ktriv⟩

end GlobalTheory
