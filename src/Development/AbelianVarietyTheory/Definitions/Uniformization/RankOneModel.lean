module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UwRQeIsNsmul

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT
noncomputable section
namespace GlobalTheory.UT.ClModel

theorem galois_all : AllU fun {_} _ _ {_} {_} {_} {_} _ _ U => Cl.Galois U := by
  intro R _ _ _ I hI D A G _ _ hG U F _ _ _ F' _ _ _ σ k hk p
  refine ⟨qkExtExists R D.toPre F F' σ.toRingHom (fun r => σ.commutes r) k p, fun x => ?_, fun p' x x' h h' =>
    GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt GlobalTheory.firstFiveLaws R I hI D A G hG U F F' σ k hk p p' x x' h h'⟩
  refine ⟨Over.homMk (spMap σ.toRingHom ≫ x.left) ?_, rfl⟩
  rw [Category.assoc, Over.w x]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  all_goals exact σ.commutes _

end GlobalTheory.UT.ClModel
end
