module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.Cris GlobalTheory.CechDR

namespace MainStatements.Hodge

def FewEqSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (n : ℕ),
    Smooth s → IsProper s →
    (∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp (IsLocalRing.ResidueField R)) (φ : X' ⟶ X),
      IsPullback φ s' s (spMap (algebraMap R (IsLocalRing.ResidueField R))) →
      Module.Finite (IsLocalRing.ResidueField R) (HO1 s') ∧
        Module.finrank (IsLocalRing.ResidueField R) (HO1 s') ≤ n) →
    ∀ M : LB X, M.IsLB → ∀ I : Ideal R, I ≠ ⊤ →
    (∀ J : Ideal R, Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) ↔ I ≤ J) →
    ∃ f : Fin n → R, Ideal.span (Set.range f) = I

def H1DimGeAbelianDim : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → Module.Finite k (HO1 A.hom) → g ≤ Module.finrank k (HO1 A.hom)

end MainStatements.Hodge
