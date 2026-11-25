module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionEqOfLawsStatement

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZH

theorem uTors_closed : GlobalTheory.ZH.UTorsSt :=
  GlobalTheory.T.uniformisation_torsion_eq_of_laws GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.2.2.1

end GlobalTheory.ZH
