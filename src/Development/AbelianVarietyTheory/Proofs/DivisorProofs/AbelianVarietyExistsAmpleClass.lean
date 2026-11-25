module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRelAmpleOfIsProjBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIsProjectiveOverRingByCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.AV

theorem exists_isAmpleCls : ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c := by
  intro K _ A
  obtain ⟨L, hL, hamp⟩ := GlobalTheory.ProjFinite.exists_relAmple_of_isProjBy
    (GlobalTheory.ProjField.isProjBy_of_isAbelianScheme K A.X A.ab)
  exact ⟨cls L hL, L, hL, hamp, rfl⟩

end GlobalTheory.AV
