module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOverStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBasisOfFormEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpandsFScale
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.TermsCompare

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (F : Type) [Field F] [Algebra (FractionRing R) F]


open GlobalTheory.FieldBaseChange GlobalTheory.ExpFieldCompare in
theorem exists_expandsF_pow {w w' : W0 U} (hw : w.IsGen) (hw' : w'.IsGen) : ∃ d : F, d ≠ 0 ∧
    ∀ (k : ℕ) t s, U.ExpandsF F k w' t s → U.ExpandsF F k w t (d ^ k • s) := by
  obtain ⟨u, hu⟩ := exists_isoVal_ratio A.isLB U.LG.isLB hw' hw
  obtain ⟨c₀, hc₀, huc⟩ := BoxExpansion.unit_const GlobalTheory.firstFiveLaws.1.globalFns A U.gen u
  refine ⟨algebraMap (FractionRing R) F c₀, (map_ne_zero _).2 hc₀, fun k t s h => ?_⟩
  obtain ⟨v, h₁, h₂⟩ := h
  have z : U.ExpandsG F k (0 : GroupSec U F k) 0 := (expandsG_iff U F k _ _).2
    ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, (Fin.sum_univ_zero _).symm,
      fun α => (map_zero _).trans (Fin.sum_univ_zero _).symm⟩
  have h₃ := expandsG_lin U F k (algebraMap (FractionRing R) F c₀ ^ k) h₂ z
  rw [add_zero, add_zero] at h₃
  refine ⟨_, ?_, h₃⟩
  refine (isoRelM_iff w (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t _).2 fun y a b ha hb => ?_
  have e := (isoRelM_iff w' (prGK G F) k (U.genF F).left h₁.1 (𝟙 _) h₁.2.1 t v).1 h₁ _ (𝟙 _) y a b ha hb
  have e₃ : (𝟙 _ ≫ prGK G F) ≫ ((Over.pullback (jK R)).obj G).hom =
      ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) ≫ jFK (R := R) F := by
    simp only [Category.id_comp]
    exact (isPullback_groupBase F).w
  have e₄ : (gm (𝟙 _ ≫ prGK G F) y ⊤ u).val = BoxExpansion.constHomVal ((𝟙 _ ≫ 𝟙 _) ≫ groupBase G F) y
      (algebraMap (FractionRing R) F c₀) :=
    ((gs_unit (𝟙 _ ≫ prGK G F) y ⊤ trivial u).symm.trans
      (congrArg (gs _ y ⊤) huc)).trans ((gs_scal _ _ y c₀).trans ((congrArg (fun q => constVal q y c₀) e₃).trans
        ((constVal_specMap _ _ y c₀).trans (BoxExpansion.constVal_eq _ _ _))))
  refine (powVal_smul (π := groupBase G F) _ v (𝟙 _ ≫ 𝟙 _) y (i := a) ha).trans ?_
  rw [e, hu _ (𝟙 _ ≫ prGK G F) y a b ha hb, mul_zpow, Units.val_mul, BoxExpansion.constVal_eq, map_pow, ← e₄,
    zpow_natCast (gm _ _ _ _), Units.val_pow_eq_pow_val, _root_.mul_assoc]


variable {F} in
theorem valAt_congr {k : ℕ} {t : SecA A F k} {x : TFK (R := R) F ⟶ A.A} {e e' : FrAt x} {c : F}
    (h : ∀ z J, Good A.L z J → val e (𝟙 _) z J = val e' (𝟙 _) z J) (H : ValAt t x e c) : ValAt t x e' c := fun z J hJ => by
  refine (H z J hJ).trans ?_
  rw [GlobalTheory.FrameMove.val_powFrame, GlobalTheory.FrameMove.val_powFrame, h z J hJ]


variable {F} in
theorem coef_smul {k : ℕ} (g : GtPtF D.toPre F) {w : Frm D.toPre F k g.b} (hw : w.IsGen) (c : F) (s : Fam D.toPre F k) (χ) :
    coef (c • s) g w χ = c * coef s g w χ := by
  have h₁ := ((CoefBasic.coef_basic R D.toPre F k g).2.2 w hw).2.1
  have h₂ : coef (0 : Fam D.toPre F k) g w χ = 0 := by
    have := h₁ 0 0 1 χ
    rw [one_smul, add_zero, _root_.one_mul] at this
    exact left_eq_add.1 this
  have := h₁ s 0 c χ
  rwa [add_zero, h₂, add_zero] at this


variable {U F} in
theorem liesOver_change {w₀ w₀' : W0 U} {d : F}
    (hd : ∀ (k : ℕ) t s, U.ExpandsF F k w₀ t s → U.ExpandsF F k w₀' t (d ^ k • s)) {g : GtPtF D.toPre F}
    {w w' : Frm D.toPre F 1 g.b} (hw' : w'.IsGen)
    (hv : ∀ z J, Good D.toPre.P.L z J → (val w (𝟙 _) z J).val = cst F z d * (val w' (𝟙 _) z J).val)
    {x : TFK (R := R) F ⟶ A.A} {e e' : FrAt x} (he : ∀ z J, Good A.L z J → val e (𝟙 _) z J = val e' (𝟙 _) z J)
    (H : LiesOver U w₀' g w' x e') : LiesOver U w₀ g w x e := by
  intro k hk wk hwk _ s s' v hs hval
  obtain ⟨W, hW, hWv⟩ := TorsionValue.exists_frm_pow w' hw' k
  have a := H k hk W hWv hW s _ v (hd k s s' hs) (valAt_congr he hval)
  have sc := TorsionValue.coef_scale (w' := wk) hW (c := d ^ k) (fun z J hJ => by
    rw [hwk z J hJ, hWv z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ, mul_pow,
      CoefBasic.cst_eq, CoefBasic.cst_eq, map_pow]) s'
  convert a using 1
  funext χ
  rw [sc, coef_smul g hW]

end

end GlobalTheory.Poinc.Sep.TermsCompare

end
