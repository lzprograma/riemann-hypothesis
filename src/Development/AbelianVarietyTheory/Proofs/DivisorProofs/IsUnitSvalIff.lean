module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TermLocus

theorem nonzeroLocus_eq : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k : ℕ) (α : D.X) (b : D.SecB k α)
    (τ : SecK D.P.L Y.q.left k), IsTermOf Y b τ → nonzeroLocus τ = Y.q.left ⁻¹ᵁ nonzeroLocus b := by
  intro R _ _ D Y k α b τ h
  ext y
  choose J hJ using fun χ : Y.H.left ⟶ D.P.A.left => exists_chart D.P.isLB (χ y)
  have hJ' : Good D.P.L y J := hJ
  have e := h Y.H (𝟙 Y.H) y J hJ'
  rw [Over.id_left, Category.id_comp] at e
  change y ∈ nonzeroLocus τ ↔ Y.q.left y ∈ nonzeroLocus b
  refine (_root_.GlobalTheory.Ex.OneGen.isUnit_sval_iff τ (𝟙 _) y hJ').symm.trans ?_
  rw [e, IsUnit.mul_iff, _root_.GlobalTheory.Ex.OneGen.isUnit_sval_iff b _ y hJ']
  exact and_iff_left (Units.isUnit _)

end GlobalTheory.Mum.TermLocus
