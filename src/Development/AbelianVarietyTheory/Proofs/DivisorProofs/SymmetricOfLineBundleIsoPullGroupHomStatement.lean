module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricOfLineBundleIsoPullGroupHom
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.symmetric_of_lineBundleIso_pull_groupHom : ∀ (S : Scheme.{0}) (H H' : Over S) [GrpObj H] [GrpObj H'] (f : H ⟶ H'), IsMonHom f → ∀ (N : LB H'.left) (M : LB H.left), N.IsLB → M.IsLB → Out.Sym H' N → LBIso (N.pull f.left) M → Out.Sym H M := by
  first | exact @GlobalTheory.sym_of_lbIso_pull_hom
