module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
theorem _root_.GlobalTheory.T.abelianScheme_laws_without_cohomology : GlobalFnsSt ∧ RigiditySt ∧ PolBaseChangeSt ∧ Semi.lemmaBSt.{0} ∧ Semi.cubical_extendsSt.{0} := by
  first | exact @GlobalTheory.laws_without_cohomology
