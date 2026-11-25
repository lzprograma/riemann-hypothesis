module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackUnique
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StalkUnitsSymmGm
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeHermitianFormExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeAdj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CompanionTheory.Ar
open Filter Topology Matrix
open scoped CategoryTheory.Obj

open GlobalTheory.TangentOrigin

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}

alias isTangent_one' := HodgeUnique.isTangent_one'

alias isDiff_one_of_fderiv := HodgeUnique.isDiff_one_of_fderiv

def transl (u : HolUnif A L g) (z : Fin g → ℂ) : A ⟶ A := (toUnit A ≫ u.ex z) * 𝟙 A

theorem ex_comp_transl (u : HolUnif A L g) (z y : Fin g → ℂ) : u.ex y ≫ transl u z = u.ex (z + y) := by
  rw [transl, MonObj.comp_mul, u.ex_add, Category.comp_id, ← Category.assoc, toUnit_unique (u.ex y ≫ toUnit A) (𝟙 _),
    Category.id_comp]

alias fderiv_eq_zero_of_isDiff_one := HodgeUnique.fderiv_eq_zero_of_isDiff_one

alias eq_zero_of_isDiff_one := HodgeUnique.eq_zero_of_isDiff_one

alias exists_affine := HodgeUnique.exists_affine

alias eq_of_isDiff := HodgeUnique.eq_of_isDiff

alias exists_linear_compare := HodgeUnique.exists_linear_compare

end Unif

section Pull

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X}
  {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left}

def push (h : IsGrpPullback A G z φ) {T : Over (Sp ℂ)} (x : T ⟶ A) : Over.mk (T.hom ≫ z) ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x]
    rfl)

alias one_left_comp := HodgeUnique.one_left_comp

def lft (h : IsGrpPullback A G z φ) (v : epsAt z ⟶ G) : epsR ℂ ⟶ A :=
  Over.homMk (h.1.lift v.left (spMap (algebraMap ℂ (DualNumber ℂ))) (Over.w v)) (h.1.lift_snd _ _ _)

theorem lft_left (h : IsGrpPullback A G z φ) (v : epsAt z ⟶ G) : (lft h v).left ≫ φ = v.left :=
  h.1.lift_fst _ _ _

theorem lft_unique (h : IsGrpPullback A G z φ) {v : epsAt z ⟶ G} {v' : epsR ℂ ⟶ A} (e : v'.left ≫ φ = v.left) :
    v' = lft h v :=
  Over.OverMorphism.ext (h.1.hom_ext (e.trans (lft_left h v).symm) (by rw [Over.w, Over.w]))

theorem isTangent_lft (h : IsGrpPullback A G z φ) {v : epsAt z ⟶ G} (hv : IsTanAt G z v) : IsTangent (lft h v) :=
  HodgeUnique.isTangent_lft h hv

end Pull

section Gen

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem exists_isRos_of_gen (hL : L.IsLB) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (t : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)) (ht : t.IsGen) :
    ∃ r : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε), GlobalTheory.TorusExt.IsRos L f g r := by
  let n : (A ⊗ A).left ⟶ (A ⊗ A).left := (lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left
  obtain ⟨r, hr, hv⟩ := exists_gen hL (φ' := rosatiφ A f g) (ε' := rosatiε)
    (fun V _ k => by
      have p := prod_ros f g (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A) k
      rw [MonObj.one_comp, MonObj.one_comp, _root_.mul_one] at p
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
        (c := ∏ i, k (rosatiφ A f g i) ^ rosatiε i) rfl (DVR.prod_neg _ _ p)) ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t n)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht n)))
  refine ⟨r, ⟨hr, corr_of_val hL fun y J hJ => ?_⟩⟩
  have e : zero2 A ≫ n = zero2 A := by
    show (lift η[A] η[A] ≫ lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left = _
    congr 1
    rw [comp_lift]
    simp [Hom.one_def]
  rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, val_one, Category.id_comp, e, mul_inv_cancel]

end Gen

section Sab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}}

theorem SAB_exists_isRos (t : SAB H S) (a : 𝓞 E) :
    ∃ r : LB.Gen (LB.LinComb t.PP.L (rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) rosatiε),
      GlobalTheory.TorusExt.IsRos t.PP.L (t.act.act a) (t.act.act (H.bar a)) r := by
  haveI := t.act.hom a
  haveI := t.act.hom (H.bar a)
  obtain ⟨u, hu⟩ := gen_of_lbIso (LBIso.symm (t.adj a))
  obtain ⟨v, hv, -⟩ := exists_gen t.PP.isLB (φ' := rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) (ε' := rosatiε)
    (fun U _ k => by
      have p := prod_ros (t.act.act a) (t.act.act (H.bar a)) (fst t.G t.G) (snd t.G t.G) k
      rw [lift_fst_snd] at p
      simp only [Over.id_left, Category.id_comp] at p
      refine (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := U) _ (prod_cube₂ _ _ k)
        (DVR.prod_neg _ _ (prod_cube₂ _ _ k))).trans (Eq.trans ?_ p.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) u hu
  exact exists_isRos_of_gen t.PP.isLB _ _ v hv

end Sab

section Fibre

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X} {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left}

theorem isCommMonObj_of_pullback [IsCommMonObj G] (h : IsGrpPullback A G z φ) : IsCommMonObj A := by
  have hc : ∀ (T : Over (Sp ℂ)) (x y : T ⟶ A), x * y = y * x := fun T x y =>
    Over.OverMorphism.ext (h.1.hom_ext (by
      rw [← h.2 T x y (push h x) (push h y) rfl rfl, ← h.2 T y x (push h y) (push h x) rfl rfl, mul_comm]) (by
      rw [Over.w, Over.w]))
  refine ⟨?_⟩
  have e := hc (A ⊗ A) (fst A A) (snd A A)
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at e
  have b : (β_ A A).hom = lift (snd A A) (fst A A) := CartesianMonoidalCategory.hom_ext _ _ (by simp) (by simp)
  rw [b]
  exact e.symm

theorem exists_endo (h : IsGrpPullback A G z φ) (f₀ : G ⟶ G) [IsMonHom f₀] :
    ∃ f : A ⟶ A, IsMonHom f ∧ f.left ≫ φ = φ ≫ f₀.left := by
  let f : A ⟶ A := Over.homMk (h.1.lift (φ ≫ f₀.left) A.hom (by rw [Category.assoc, Over.w, h.1.w])) (h.1.lift_snd _ _ _)
  have hf : f.left ≫ φ = φ ≫ f₀.left := h.1.lift_fst _ _ _
  refine ⟨f, isMonHom_of_mul _ fun T x y => ?_, hf⟩
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))
  have e1 := h.2 T x y (push h x) (push h y) rfl rfl
  have e2 := h.2 T (x ≫ f) (y ≫ f) (push h x ≫ f₀) (push h y ≫ f₀)
    (by simp [push, hf]) (by simp [push, hf])
  rw [Over.comp_left, Category.assoc, hf, ← Category.assoc, ← e1, ← e2, ← Over.comp_left, MonObj.mul_comp]

end Fibre

theorem isTanAt_comp {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Sp ℂ ⟶ X} (f : G ⟶ G) [IsMonHom f]
    {v : epsAt z ⟶ G} (hv : IsTanAt G z v) : IsTanAt G z (v ≫ f) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

end GlobalTheory.CompanionTheory.Ar.HodgeAdj

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HodgeAdj

theorem hodgeInnerProduct_act_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ t.G) (a : 𝓞 E) (c : ℂ), (∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' t z), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L) → IsTanAt t.G z v → IsTanAt t.G z w → (HodgeIP t.G t.PP.L z (v ≫ t.act.act a) w c ↔ HodgeIP t.G t.PP.L z v (w ≫ t.act.act (H.bar a)) c) := by
  intro E _ _ _ H X t z v w a c hfib hv hw
  obtain ⟨V, _, _, ⟨M⟩⟩ := lieModel_exists X t.G ℂ z
  obtain ⟨h, hh, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.exists_hodgeInnerProduct_form E H X t z V M hfib
  haveI := t.act.hom a
  haveI := t.act.hom (H.bar a)
  obtain ⟨x', hx'⟩ := M.onto _ (isTanAt_comp (t.act.act a) hv)
  obtain ⟨y', hy'⟩ := M.onto _ (isTanAt_comp (t.act.act (H.bar a)) hw)
  obtain ⟨x, rfl⟩ := M.onto v hv
  obtain ⟨y, rfl⟩ := M.onto w hw
  rw [← hx', ← hy', hh, hh]
  suffices e : h x' y = h x y' by rw [e]
  obtain ⟨hL, -, -, A, _, φ, g, u, Hm, χ, v₁, w₁, α, β, hpb, hAH, e₁, e₂, d₁, d₂, -⟩ := (hh x y _).2 rfl
  haveI := isCommMonObj_of_pullback hpb
  obtain ⟨f, _, hf⟩ := exists_endo hpb (t.act.act a)
  obtain ⟨f', _, hf'⟩ := exists_endo hpb (t.act.act (H.bar a))
  obtain ⟨F, hF⟩ := exists_linear_compare u u f
  obtain ⟨F', hF'⟩ := exists_linear_compare u u f'
  obtain ⟨r, hr⟩ := SAB_exists_isRos t a
  have hLφ : (t.PP.L.pull φ).IsLB := LB.isLB_pull t.PP.isLB φ
  obtain ⟨wi, hwi⟩ := GlobalTheory.PolBaseChange.lbIso_refl hLφ
  obtain ⟨s, hs, -⟩ := GlobalTheory.Ex.Arch.FibRos.exists_ros_down hpb t.PP.isLB hLφ hwi (MonObj.one_comp _) (MonObj.one_comp _) hf hf' hr
  have adj := (GlobalTheory.FrameValue.genVal_rosati hLφ hAH hF hF' s hs.1 hs.2).1
  have t₁ : IsTangent v₁ := by
    rw [lft_unique hpb e₁]
    exact isTangent_lft hpb (M.tan x)
  have t₂ : IsTangent w₁ := by
    rw [lft_unique hpb e₂]
    exact isTangent_lft hpb (M.tan y)
  have c₁ : HodgeIP t.G t.PP.L z (M.pt x') (M.pt y) (Real.pi * (β ⬝ᵥ Hm.mulVec (star (F α)))) :=
    ⟨hL, M.tan _, M.tan _, A, inferInstance, φ, g, u, Hm, χ, v₁ ≫ f, w₁, F α, β, hpb, hAH,
      by rw [hx', Over.comp_left, Over.comp_left, Category.assoc, hf, ← Category.assoc, e₁], e₂,
      GlobalTheory.HomLinear.isDiff_comp u u f F hF t₁ d₁, d₂, rfl⟩
  have c₂ : HodgeIP t.G t.PP.L z (M.pt x) (M.pt y') (Real.pi * (F' β ⬝ᵥ Hm.mulVec (star α))) :=
    ⟨hL, M.tan _, M.tan _, A, inferInstance, φ, g, u, Hm, χ, v₁, w₁ ≫ f', α, F' β, hpb, hAH, e₁,
      by rw [hy', Over.comp_left, Over.comp_left, Category.assoc, hf', ← Category.assoc, e₂], d₁,
      GlobalTheory.HomLinear.isDiff_comp u u f' F' hF' t₂ d₂, rfl⟩
  rw [← (hh _ _ _).1 c₁, ← (hh _ _ _).1 c₂]
  congr 1
  have := congrArg (starRingEnd ℂ) (adj α β)
  rwa [conj_hermForm hAH.1, conj_hermForm hAH.1] at this

end GlobalTheory.CompanionTheory.Ar
