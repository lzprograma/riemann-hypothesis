module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSymmetricSquareRoot
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem _root_.GlobalTheory.T.exists_principalPolarization_symmetric_squareRoot : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (L : LB c.A.left), c.Principal → SmoothOfRelativeDimension h c.A.hom → L.IsLB → LBIso (abelian₂ c.A L) c.P → LBIso L (L.pull (GrpObj.inv : c.A ⟶ c.A).left) → ∃ (P : Out.PolAV (Sp R)) (φ : P.A.left ⟶ c.A.left), SqOf P c (𝟙 _) φ := by
  first | exact @GlobalTheory.SymRoot.exists_polAV_sqOf
