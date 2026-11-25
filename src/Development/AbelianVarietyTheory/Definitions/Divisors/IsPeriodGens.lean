module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj

namespace GlobalTheory.UCanon

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev prj {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {θ : R →+* R'} {D : DegPre R} {D' : DegPre R'}
    (h : IsPullDeg θ D D') : D'.P.A.left ⟶ D.P.A.left :=
  h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf θ)

variable {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) {V : Type} [CommRing V] [IsDomain V]
  (Q : DegPre V) [Module (𝓞 E) Q.X] (oQ : letI := H.starRing; Q.OAct (𝓞 E)) (iw : L.W →+* V) {I : Type} [Fintype I]
  (s : I → V) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : Q.X ≃ₗ[𝓞 E] L.D.X)

def DivBy (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw (mulDeg L.D l.M') (GlobalTheory.PolDeg.rescale Q g)) : Prop :=
  (∀ y, (((g y)⁻¹ : (FractionRing V)ˣ) : FractionRing V) =
      ∏ k, algebraMap V (FractionRing V) (s k) ^ ((l.M' : ℤ) * ε k (e y) (H.w0 • e y))) ∧
    (∀ y : Q.X, hD.xe y = e y) ∧
    (letI := H.starRing; ∀ x : 𝓞 E, (oQ.onB.act x).left ≫ hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) =
      hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) ≫ (L.oa.onB.act x).left)

variable {Q} {g : Q.X → (FractionRing V)ˣ} (hD : IsPullDeg iw (mulDeg L.D l.M') (GlobalTheory.PolDeg.rescale Q g))

def IsLevPt (a : D'.La) (p : QkPt Q (FractionRing V) l.M') : Prop :=
  p.y = 0 ∧ p.g.b.left ≫ (hD.e.hom.left ≫ pullback.fst L.D.P.A.hom (specOf iw) : Q.P.A.left ⟶ L.D.P.A.left) =
    jK V ≫ spMap iw ≫ (L.o.etaA a).left ≫ L.φB

end GlobalTheory.UCanon
