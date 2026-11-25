module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Edge1
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv

@[expose] public section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential GlobalTheory.W1 GlobalTheory.WH

private theorem isIntegral_map_iff {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L]
    [IsScalarTower ℂ K L] (B : Subalgebra ℂ K) (y : L) :
    IsIntegral (B.map (IsScalarTower.toAlgHom ℂ K L)) y ↔ IsIntegral B y := by
  let j := IsScalarTower.toAlgHom ℂ K L
  exact ((B.equivMapOfInjective j j.toRingHom.injective).toRingEquiv.isIntegral_iff rfl y).symm

private theorem dualNumberPoint_preimage_top_of_reduction {d : ℕ} {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ}
    [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] {c : Y ⟶ Z} (hc : c ≫ s = s') [IsFinite c] [Etale c]
    [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s')
    (j : Z.functionField →ₐ[ℂ] Y.functionField)
    (hj : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
      j ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom (c.app V g))
    {F : Type} [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [IsScalarTower ℂ F Z.functionField]
    (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x)
    (hU : IsAffCover s U (rB ℂ Z.functionField x)) :
    IsAffCover s' (fun i => c ⁻¹ᵁ U i) (R2 x j) := by
  letI : Algebra Z.functionField Y.functionField := j.toRingHom.toAlgebra
  letI : Algebra F Y.functionField :=
    ((algebraMap Z.functionField Y.functionField).comp (algebraMap F Z.functionField)).toAlgebra
  haveI : IsScalarTower ℂ Z.functionField Y.functionField := .of_algebraMap_eq fun r => (j.commutes r).symm
  haveI : IsScalarTower F Z.functionField Y.functionField := .of_algebraMap_eq fun r => rfl
  haveI : IsScalarTower ℂ F Y.functionField := .of_algebraMap_eq fun r => by
    change algebraMap ℂ Y.functionField r = j (algebraMap F Z.functionField (algebraMap ℂ F r))
    rw [← IsScalarTower.algebraMap_apply ℂ F Z.functionField, j.commutes]
  have hjeq : IsScalarTower.toAlgHom ℂ Z.functionField Y.functionField = j := AlgHom.ext fun _ => rfl
  have e : rB ℂ Y.functionField x = R2 x j := by
    funext I
    ext y
    change IsIntegral (rA ℂ x I) y ↔ IsIntegral ((rB ℂ Z.functionField x I).map j) y
    rw [UpperTheory.A.isIntegral_rB_iff (K := Z.functionField) x I y, ← hjeq, isIntegral_map_iff]
  rw [← e]
  exact (UpperTheory.A.isFinCover_pull hc hK hL (fun V hV hV' g => (hj V hV hV' g).symm) hx hU).2

theorem UpperTheory.etaleCorrespondence_functionField_statement_one :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (_ : IsProjOver s) (c1 c2 : Y ⟶ Z) (_ : c1 ≫ s = s') (_ : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (_ : instK = ffAlg s) (_ : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (_ : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (_ : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (_ : IsFinCover ℂ Z.functionField x) (_ : IsAffCover s U (rB ℂ Z.functionField x)), IsAffCover s' (fun i => c2 ⁻¹ᵁ U i) (R2 x j2) := by
  intro d Z Y _ _ s s' _ _ hP c1 c2 h1 h2 _ _ _ _ instK instL hK hL _ _ g1 j2 g2 F _ _ _ _ _ _ _ x U hx hU
  exact dualNumberPoint_preimage_top_of_reduction h2 hK hL j2 g2 x U hx hU
