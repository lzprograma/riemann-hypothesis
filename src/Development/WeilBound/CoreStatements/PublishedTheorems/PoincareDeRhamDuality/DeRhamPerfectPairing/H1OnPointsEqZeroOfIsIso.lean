module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic

namespace CrystallinePoints.Pd

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}

theorem hom_ext' {s : X ⟶ Sp R} {P Q : Pt s} {φ ψ : P.Hom Q} (h : ∀ b, φ.ρ b = ψ.ρ b) : φ = ψ := by
  obtain ⟨ρ, e⟩ := φ
  obtain ⟨ρ', e'⟩ := ψ
  obtain rfl : ρ = ρ' := AlgHom.ext h
  rfl

instance ptCat (s : X ⟶ Sp R) : Category.{0} (Pt s) where
  Hom := Pt.Hom
  id := Pt.Hom.id
  comp := Pt.Hom.comp
  id_comp _ := hom_ext' fun _ ↦ rfl
  comp_id _ := hom_ext' fun _ ↦ rfl
  assoc _ _ _ := hom_ext' fun _ ↦ rfl

@[reducible] def FP (s : X ⟶ Sp R) : Pt s ⥤ CommAlgCat.{0} R where
  obj P := CommAlgCat.of R P.B
  map φ := CommAlgCat.ofHom φ.ρ

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {φ : X' ⟶ X}

@[reducible] def pushPt (h : φ ≫ s = s' ≫ spMap σ) (P : Pt s') : Pt s where
  B := P.B
  alg := ((algebraMap R' P.B).comp σ).toAlgebra
  x := P.x ≫ φ
  w := by rw [Category.assoc, h, ← Category.assoc, P.w, ← GlobalTheory.Cris.spMap_comp]

def pushHom (h : φ ≫ s = s' ≫ spMap σ) {P Q : Pt s'} (f : P ⟶ Q) : pushPt h P ⟶ pushPt h Q where
  ρ := { (f.ρ : P.B →+* Q.B) with commutes' := fun r ↦ f.ρ.commutes (σ r) }
  pt := by
    change spMap (f.ρ : P.B →+* Q.B) ≫ P.x ≫ φ = Q.x ≫ φ
    rw [← Category.assoc, f.pt]

end CrystallinePoints.Pd
