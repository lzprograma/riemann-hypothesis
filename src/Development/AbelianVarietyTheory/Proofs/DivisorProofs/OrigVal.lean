module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkOfInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

def OrigVal {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {k : ℕ} {α : D.X} (b : D.SecB k α) (v : R) : Prop :=
  ∀ (z : Sp R) (J : (Sp R ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    sval b (unitW D.P.A) z J = stalkOf z v * (val D.rig (idW R) z J).val ^ k

end GlobalTheory.Mum
