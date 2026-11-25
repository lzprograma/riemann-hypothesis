module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVarProj

theorem strHom_eq_and_isProjOver : ∀ (K : Type) [Field K] (A : AbVar K),
    (letI := A.algΓ; GlobalTheory.strHom K A.X.left = A.X.hom) ∧ IsProjOver A.X.hom := by
  intro K _ A
  refine ⟨?_, ?_⟩
  · letI := A.algΓ
    exact GlobalTheory.strHom_eq fun _ => rfl
  · exact (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.X.hom).1
      (GlobalTheory.ProjField.isProjBy_of_isAbelianScheme K A.X A.ab)

end GlobalTheory.AV.AbVarProj
