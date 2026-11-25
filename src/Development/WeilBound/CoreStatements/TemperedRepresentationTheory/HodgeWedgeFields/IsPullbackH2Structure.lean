module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace MainStatements.Hodge

def IsPullbackH2Structure {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
    {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) (c : GlobalTheory.CatCoh.H2 (OAff s)) (c' : GlobalTheory.CatCoh.H2 (OAff s')) : Prop :=
  (pairPull h).pull2 c = (pairRes φ s').pull2 c'

def HopfLeSt : Prop := AllFin fun R _ _ _ F ↦ ∀ g : ℕ, IsField R → Stein F →
  (∀ n, g ≤ n → Function.Exact (dn F n) (dn F (n + 1))) → Hopf F True →
  ∀ x : Fin (g + 1) → GlobalTheory.CatCoh.H1 F, ¬ LinearIndependent R x

end MainStatements.Hodge
