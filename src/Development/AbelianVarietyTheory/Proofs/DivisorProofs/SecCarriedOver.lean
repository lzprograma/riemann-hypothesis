module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

def IsSecOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (s : ∀ k, Γ(X, W ⊓ L.U k)) : Prop :=
  ∀ (z : X) (k k' : L.ι), z ∈ W → z ∈ L.U k → z ∈ L.U k' →
    gs (𝟙 X) z (W ⊓ L.U k) (s k) =
      (gm (𝟙 X) z (L.U k ⊓ L.U k') (L.g k k') : X.presheaf.stalk z) * gs (𝟙 X) z (W ⊓ L.U k') (s k')

def SecCarriedOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (s : ∀ k, Γ(X, W ⊓ L.U k)) (f : X ⟶ X)
    (w : LB.Iso L (L.pull f)) : Prop :=
  ∀ (z : X) (j k : L.ι), z ∈ W → f z ∈ W → z ∈ L.U k → f z ∈ L.U j →
    gs f z (W ⊓ L.U j) (s j) = (gw w (𝟙 X) z j k : X.presheaf.stalk z) * gs (𝟙 X) z (W ⊓ L.U k) (s k)

end GlobalTheory.Mum
