module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsClosed

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT

namespace GlobalTheory.TorsionIso

theorem torsion_clause :
    AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Torsion U := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _ k hk
  obtain ⟨f, hf⟩ := exists_tors_closed R I hI D A G hG U F k hk
  refine ⟨f, hf, fun p => ?_⟩
  obtain ⟨w, hw⟩ := U.toUnifPre.ext
  exact ((hf.1 p (f p)).2 rfl w hw).1

end GlobalTheory.TorsionIso
