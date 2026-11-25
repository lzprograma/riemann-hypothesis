module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEndomorphismActionUniformizationData
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT

namespace GlobalTheory.UT



theorem functorial_of_unif :
    AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Functorial U := by
  have hL := GlobalTheory.firstFiveLaws
  obtain ⟨-, h1, h2, h3, h4⟩ := GlobalTheory.twistBaseChange_and_valuation_statements
  have hex := @GlobalTheory.EndData.exists_endU hL
  have hros := @GlobalTheory.UT.rosatiAdj_and_c_linear_of_endU hL
  have hcalc := @GlobalTheory.EndCalc.end_calculus hL
  have hbal := @GlobalTheory.Balanced.main hL h1 h2 h3 h4
  intro R _ _ _ I hB D A G _ _ hG U
  refine ⟨hex R I hB D A G hG U, fun E E' hE => ⟨hros R I hB D A G hG U E E' hE, fun F _ _ _ => ?_⟩⟩
  exact ⟨(hcalc R I hB D A G hG U F E E E).1, hbal R I hB D A G hG U F E E' hE⟩

end GlobalTheory.UT
