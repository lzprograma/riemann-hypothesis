module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic GlobalTheory.RealMult


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G]
    (f : G' ⟶ G) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G (𝟙 S) f.left) {T : Over S} (x y : T ⟶ G') :
    (x * y) ≫ f = (x ≫ f) * (y ≫ f) := by
  have H := h.2 T x y
  revert H
  generalize hg : T.hom ≫ 𝟙 S = g
  rw [Category.comp_id] at hg
  subst hg
  intro H
  exact Over.OverMorphism.ext (H (x ≫ f) (y ≫ f) rfl rfl).symm


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
alias _root_.GlobalTheory.AmpleRigid.isMonHom_of_mul_comp := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul

end GlobalTheory.AmpleRigid
