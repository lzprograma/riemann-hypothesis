module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GlueModelsOverSubfield
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.SpreadScheme

open GlobalTheory.Spread GlobalTheory.GlueModels

section Iso

variable {k V : Type} [CommRing k] [CommRing V] [Algebra k V] {P Q T : Scheme.{0}}
  {p : P ⟶ Sp k} {q : Q ⟶ Sp k} {t : T ⟶ Sp V} {τ : T ⟶ P} {τ' : T ⟶ Q}

theorem eq_comp_bcMap (hτ : IsPullback τ t p (spMap (algebraMap k V)))
    (R : Subalgebra k V) (σ : T ⟶ pullback p (spMap (algebraMap k R)))
    (h₁ : σ ≫ pullback.fst _ _ = τ) (h₂ : σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom) :
    σ = hτ.isoPullback.hom ≫ bcMap p R.val := by
  apply pullback.hom_ext
  · rw [h₁, Category.assoc, bcMap_fst, IsPullback.isoPullback_hom_fst]
  · rw [h₂, Category.assoc, bcMap_snd, IsPullback.isoPullback_hom_snd_assoc]

def up {R R' : Subalgebra k V} (h : R ≤ R') (ψ : pullback p (spMap (algebraMap k R)) ⟶ Q)
    (hψ : ψ ≫ q = pullback.fst _ _ ≫ p) :
    pullback p (spMap (algebraMap k R')) ⟶ pullback q (spMap (algebraMap k R')) :=
  pullback.lift (bcMap p (Subalgebra.inclusion h) ≫ ψ) (pullback.snd _ _)
    (by rw [Category.assoc, hψ, bcMap_fst_assoc, pullback.condition])

theorem up_fst {R R' : Subalgebra k V} (h : R ≤ R') (ψ : pullback p (spMap (algebraMap k R)) ⟶ Q)
    (hψ : ψ ≫ q = pullback.fst _ _ ≫ p) :
    up h ψ hψ ≫ pullback.fst _ _ = bcMap p (Subalgebra.inclusion h) ≫ ψ := pullback.lift_fst _ _ _

@[reassoc]
theorem up_snd {R R' : Subalgebra k V} (h : R ≤ R') (ψ : pullback p (spMap (algebraMap k R)) ⟶ Q)
    (hψ : ψ ≫ q = pullback.fst _ _ ≫ p) :
    up h ψ hψ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

@[reassoc]
theorem up_bcMap {R R' R'' : Subalgebra k V} (h : R ≤ R') (h' : R' ≤ R'')
    (ψ : pullback p (spMap (algebraMap k R)) ⟶ Q) (hψ : ψ ≫ q = pullback.fst _ _ ≫ p) :
    up (h.trans h') ψ hψ ≫ bcMap q (Subalgebra.inclusion h') =
      bcMap p (Subalgebra.inclusion h') ≫ up h ψ hψ := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, up_fst, Category.assoc, up_fst,
      bcMap_comp_of_eq_assoc p _ _ (Subalgebra.inclusion (h.trans h')) fun _ ↦ rfl]
  · rw [Category.assoc, bcMap_snd, up_snd_assoc, Category.assoc, up_snd, bcMap_snd]

theorem exists_up_comp_up [LocallyOfFiniteType p] [QuasiCompact p]
    (hτ : IsPullback τ t p (spMap (algebraMap k V)))
    (hτ' : IsPullback τ' t q (spMap (algebraMap k V))) {R₁ R₂ : Subalgebra k V} (hR₁ : R₁.FG) (hR₂ : R₂.FG)
    (ψ : pullback p (spMap (algebraMap k R₁)) ⟶ Q) (hψ : ψ ≫ q = pullback.fst _ _ ≫ p)
    (χ : pullback q (spMap (algebraMap k R₂)) ⟶ P) (hχ : χ ≫ p = pullback.fst _ _ ≫ q)
    (hψ' : bcMap p R₁.val ≫ ψ = hτ.isoPullback.inv ≫ τ')
    (hχ' : bcMap q R₂.val ≫ χ = hτ'.isoPullback.inv ≫ τ) :
    ∃ R : Subalgebra k V, R.FG ∧ ∀ (R' : Subalgebra k V) (h₁ : R₁ ≤ R') (h₂ : R₂ ≤ R'), R ≤ R' →
      up h₁ ψ hψ ≫ up h₂ χ hχ = 𝟙 _ := by
  have l₁ : R₁ ≤ R₁ ⊔ R₂ := le_sup_left
  have l₂ : R₂ ≤ R₁ ⊔ R₂ := le_sup_right
  have h : hτ.isoPullback.hom ≫ bcMap p (R₁ ⊔ R₂).val ≫ up l₁ ψ hψ =
      hτ'.isoPullback.hom ≫ bcMap q (R₁ ⊔ R₂).val := by
    apply eq_comp_bcMap hτ'
    · rw [Category.assoc, Category.assoc, up_fst, bcMap_comp_of_eq_assoc p _ _ R₁.val fun _ ↦ rfl, hψ',
        Iso.hom_inv_id_assoc]
    · rw [Category.assoc, Category.assoc, up_snd, bcMap_snd, IsPullback.isoPullback_hom_snd_assoc]
  obtain ⟨R, hle, hR, e⟩ := exists_fg_comp_eq_comp p p (R₁ ⊔ R₂) (hR₁.sup hR₂)
    (up l₁ ψ hψ ≫ up l₂ χ hχ ≫ pullback.fst _ _) (pullback.fst _ _)
    (by rw [Category.assoc, Category.assoc, pullback.condition, up_snd_assoc, up_snd_assoc]) rfl
    (by rw [← cancel_epi hτ.isoPullback.hom, reassoc_of% h, up_fst,
      bcMap_comp_of_eq_assoc q _ _ R₂.val fun _ ↦ rfl, hχ', Iso.hom_inv_id_assoc, bcMap_fst,
      IsPullback.isoPullback_hom_fst])
  refine ⟨R, hR, fun R' h₁ h₂ h₃ ↦ ?_⟩
  apply pullback.hom_ext
  · have e' := congr(bcMap p (Subalgebra.inclusion h₃) ≫ $e)
    rw [bcMap_comp_of_eq_assoc p _ _ (Subalgebra.inclusion (hle.trans h₃)) fun _ ↦ rfl,
      ← up_bcMap_assoc, ← up_bcMap_assoc, bcMap_fst, bcMap_fst, bcMap_fst] at e'
    rw [Category.assoc, Category.id_comp]
    exact e'
  · rw [Category.assoc, up_snd, up_snd, Category.id_comp]

theorem models_iso [LocallyOfFinitePresentation p] [QuasiSeparated p] [QuasiCompact p]
    [LocallyOfFinitePresentation q] [QuasiSeparated q] [QuasiCompact q]
    (hτ : IsPullback τ t p (spMap (algebraMap k V))) (hτ' : IsPullback τ' t q (spMap (algebraMap k V))) :
    ∃ (R : Subalgebra k V) (e : pullback p (spMap (algebraMap k R)) ≅ pullback q (spMap (algebraMap k R))),
      R.FG ∧ e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      ∀ σ : T ⟶ pullback p (spMap (algebraMap k R)), σ ≫ pullback.fst _ _ = τ →
        σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom → σ ≫ e.hom ≫ pullback.fst _ _ = τ' := by
  obtain ⟨R₁, ψ, hR₁, hψ, hψ'⟩ := exists_fg_comp_eq p q (hτ.isoPullback.inv ≫ τ') (by
    rw [Category.assoc, hτ'.w, ← hτ.w, IsPullback.isoPullback_inv_fst_assoc])
  obtain ⟨R₂, χ, hR₂, hχ, hχ'⟩ := exists_fg_comp_eq q p (hτ'.isoPullback.inv ≫ τ) (by
    rw [Category.assoc, hτ.w, ← hτ'.w, IsPullback.isoPullback_inv_fst_assoc])
  obtain ⟨R₃, hR₃, e₃⟩ := exists_up_comp_up hτ hτ' hR₁ hR₂ ψ hψ χ hχ hψ' hχ'
  obtain ⟨R₄, hR₄, e₄⟩ := exists_up_comp_up hτ' hτ hR₂ hR₁ χ hχ ψ hψ hχ' hψ'
  let R : Subalgebra k V := (R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄)
  have l₁ : R₁ ≤ R := le_sup_left.trans le_sup_left
  have l₂ : R₂ ≤ R := le_sup_right.trans le_sup_left
  refine ⟨R, ⟨up l₁ ψ hψ, up l₂ χ hχ, e₃ R l₁ l₂ (le_sup_left.trans le_sup_right),
    e₄ R l₂ l₁ (le_sup_right.trans le_sup_right)⟩, (hR₁.sup hR₂).sup (hR₃.sup hR₄), up_snd l₁ ψ hψ,
    fun σ h₁ h₂ ↦ ?_⟩
  rw [eq_comp_bcMap hτ R σ h₁ h₂, Category.assoc]
  change _ ≫ _ ≫ up l₁ ψ hψ ≫ _ = _
  rw [up_fst, bcMap_comp_of_eq_assoc p _ _ R₁.val fun _ ↦ rfl, hψ', Iso.hom_inv_id_assoc]

end Iso

def HasModel (P Q : MorphismProperty Scheme.{0}) {V : Type} [CommRing V] {X : Scheme.{0}} (p : X ⟶ Sp V) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (f : R →+* V) (X₀ : Scheme.{0}) (p₀ : X₀ ⟶ Sp R) (φ : X ⟶ X₀),
    Algebra.FiniteType ℤ R ∧ P p₀ ∧ Q p₀ ∧ QuasiCompact p₀ ∧ IsPullback φ p p₀ (spMap f)

structure PairModel (P Q : MorphismProperty Scheme.{0}) {S S₀ U T : Scheme.{0}} (f : S ⟶ S₀) (p : U ⟶ S) (a : T ⟶ U) where
  U₀ : Scheme.{0}
  T₀ : Scheme.{0}
  p₀ : U₀ ⟶ S₀
  a₀ : T₀ ⟶ U₀
  φ : U ⟶ U₀
  τ : T ⟶ T₀
  hP : P p₀
  hQ : Q p₀
  qc : QuasiCompact p₀
  opn : IsOpenImmersion a₀
  qca : QuasiCompact a₀
  hφ : IsPullback φ p p₀ f
  hτ : IsPullback τ a a₀ φ

attribute [instance] PairModel.qc PairModel.opn PairModel.qca

variable {S S₁ S₀ U T : Scheme.{0}} {f : S ⟶ S₀} {p : U ⟶ S} {a : T ⟶ U}

theorem isPullback_lift {X X₀ : Scheme.{0}} {q : X ⟶ S} {q₀ : X₀ ⟶ S₀} {φ : X ⟶ X₀} (h : IsPullback φ q q₀ f)
    (σ : S ⟶ S₁) (g : S₁ ⟶ S₀) (e : σ ≫ g = f) :
    IsPullback (pullback.lift φ (q ≫ σ) (by rw [Category.assoc, e, h.w])) q (pullback.snd q₀ g) σ := by
  refine IsPullback.of_right (h₁₂ := pullback.fst q₀ g) (v₁₃ := q₀) (h₂₂ := g) ?_ (pullback.lift_snd _ _ _)
    (.of_hasPullback _ _)
  rw [pullback.lift_fst, e]
  exact h

def PairModel.baseChange {P Q : MorphismProperty Scheme.{0}} [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
    (M : PairModel P Q f p a) (σ : S ⟶ S₁) (g : S₁ ⟶ S₀) (e : σ ≫ g = f) : PairModel P Q σ p a :=
  have w : M.τ ≫ M.a₀ ≫ M.p₀ = ((a ≫ p) ≫ σ) ≫ g := by
    rw [M.hτ.w_assoc, M.hφ.w, Category.assoc, Category.assoc, e]
  let a₁ : pullback (M.a₀ ≫ M.p₀) g ⟶ pullback M.p₀ g :=
    pullback.lift (pullback.fst _ _ ≫ M.a₀) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
  have h₁ : IsPullback (pullback.fst _ _) a₁ M.a₀ (pullback.fst _ _) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (.of_hasPullback M.p₀ g)
    rw [pullback.lift_snd]
    exact .of_hasPullback _ _
  { U₀ := pullback M.p₀ g
    T₀ := pullback (M.a₀ ≫ M.p₀) g
    p₀ := pullback.snd _ _
    a₀ := a₁
    φ := pullback.lift M.φ (p ≫ σ) (by rw [Category.assoc, e, M.hφ.w])
    τ := pullback.lift M.τ ((a ≫ p) ≫ σ) w
    hP := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P) (.of_hasPullback M.p₀ g) M.hP
    hQ := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := Q) (.of_hasPullback M.p₀ g) M.hQ
    qc := inferInstance
    opn := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₁ M.opn
    qca := MorphismProperty.of_isPullback (P := @QuasiCompact) h₁ M.qca
    hφ := isPullback_lift M.hφ σ g e
    hτ := by
      refine IsPullback.of_right ?_ ?_ h₁
      · rw [pullback.lift_fst, pullback.lift_fst]
        exact M.hτ
      · apply pullback.hom_ext
        · simp only [a₁, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, M.hτ.w]
        · simp only [a₁, Category.assoc, pullback.lift_snd] }

theorem PairModel.baseChange_a₀_p₀ {P Q : MorphismProperty Scheme.{0}} [P.IsStableUnderBaseChange]
    [Q.IsStableUnderBaseChange] (M : PairModel P Q f p a) (σ : S ⟶ S₁) (g : S₁ ⟶ S₀) (e : σ ≫ g = f) :
    (M.baseChange σ g e).a₀ ≫ (M.baseChange σ g e).p₀ = pullback.snd (M.a₀ ≫ M.p₀) g :=
  pullback.lift_snd _ _ _

theorem of_two (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtSource P] {X W : Scheme.{0}}
    {u : U ⟶ X} {v : W ⟶ X} [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) (q : X ⟶ S) (hu : P (u ≫ q)) (hv : P (v ≫ q)) :
    P q := by
  let Y : Bool → Scheme.{0} := fun i => Bool.rec U W i
  let t : ∀ i, Y i ⟶ X := fun i => Bool.rec (motive := fun i => Y i ⟶ X) u v i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers Bool Y t (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)
  refine IsZariskiLocalAtSource.of_openCover (P := P) 𝒰 ?_
  rintro (_ | _)
  · exact hu
  · exact hv

theorem exists_glued {P Q : MorphismProperty Scheme.{0}} [IsZariskiLocalAtSource P]
    {X W : Scheme.{0}} (q : X ⟶ S) {u : U ⟶ X} {v : W ⟶ X} [IsOpenImmersion u] [IsOpenImmersion v]
    {b : T ⟶ W} (h : IsPullback a b u v) (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v)
    (M : PairModel P Q f (u ≫ q) a) (N : PairModel P Q f (v ≫ q) b) (e : M.T₀ ≅ N.T₀) (he : M.τ ≫ e.hom = N.τ)
    (he' : e.hom ≫ N.a₀ ≫ N.p₀ = M.a₀ ≫ M.p₀) [CompactSpace S₀] [QuasiSeparatedSpace S₀] :
    ∃ (X₀ : Scheme.{0}) (q₀ : X₀ ⟶ S₀) (φ : X ⟶ X₀), P q₀ ∧ QuasiCompact q₀ ∧ IsPullback φ q q₀ f := by
  have Hp := M.hτ
  have Hq : IsPullback M.τ b (e.hom ≫ N.a₀) N.φ :=
    N.hτ.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) (by simp [← he]) (by simp) (by simp) (by simp)
  have := isOpenImmersion_inl M.a₀ (e.hom ≫ N.a₀)
  have := isOpenImmersion_inr M.a₀ (e.hom ≫ N.a₀)
  obtain ⟨φ, h1, h2⟩ := exists_glue h hc (M.φ ≫ pushout.inl M.a₀ (e.hom ≫ N.a₀))
    (N.φ ≫ pushout.inr M.a₀ (e.hom ≫ N.a₀)) (by
    rw [← Hp.w_assoc, ← Hq.w_assoc, pushout.condition])
  have e1 (x : U) : φ (u x) = pushout.inl M.a₀ (e.hom ≫ N.a₀) (M.φ x) := congrArg (fun g => g x) h1
  have e2 (x : W) : φ (v x) = pushout.inr M.a₀ (e.hom ≫ N.a₀) (N.φ x) := congrArg (fun g => g x) h2
  have e3 (w : T) : u (a w) = v (b w) := congrArg (fun g => g w) h.w
  have hcov := pushout_cover M.a₀ (e.hom ≫ N.a₀)
  refine ⟨_, pushout.desc M.p₀ N.p₀ (by rw [Category.assoc, he']), φ, ?_, ?_, ?_⟩
  · refine of_two P hcov _ ?_ ?_
    · rw [pushout.inl_desc]
      exact M.hP
    · rw [pushout.inr_desc]
      exact N.hP
  · have : CompactSpace M.U₀ := QuasiCompact.compactSpace_of_compactSpace M.p₀
    have : CompactSpace N.U₀ := QuasiCompact.compactSpace_of_compactSpace N.p₀
    have : CompactSpace (pushout M.a₀ (e.hom ≫ N.a₀) : Scheme.{0}) := by
      refine ⟨?_⟩
      rw [← Set.eq_univ_of_forall (s := Set.range (pushout.inl M.a₀ (e.hom ≫ N.a₀)) ∪
        Set.range (pushout.inr M.a₀ (e.hom ≫ N.a₀))) hcov]
      exact (isCompact_range (Scheme.Hom.continuous _)).union (isCompact_range (Scheme.Hom.continuous _))
    infer_instance
  refine isPullback_of_two hcov (u' := u) (v' := v) (aU := M.φ) (aV := N.φ) ?_ ?_ ?_ ?_
  · refine IsOpenImmersion.isPullback _ _ _ _ h1 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with hx | ⟨x, rfl⟩
      · exact hx
      · obtain ⟨w, -, hw⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e2 x))
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback Hq w x hw
        exact ⟨a z, e3 z⟩
    · rintro ⟨y, rfl⟩
      exact ⟨M.φ y, (e1 y).symm⟩
  · refine IsOpenImmersion.isPullback _ _ _ _ h2 ?_
    ext x
    constructor
    · rintro ⟨y, hy⟩
      rcases hc x with ⟨x, rfl⟩ | hx
      · obtain ⟨w, hw, -⟩ := exists_of_inl_eq_inr _ _ (hy.trans (e1 x)).symm
        obtain ⟨z, -, rfl⟩ := Scheme.exists_preimage_of_isPullback Hp w x hw
        exact ⟨b z, (e3 z).symm⟩
      · exact hx
    · rintro ⟨y, rfl⟩
      exact ⟨N.φ y, (e2 y).symm⟩
  · simpa only [pushout.inl_desc] using M.hφ
  · simpa only [pushout.inr_desc] using N.hφ

variable {V : Type} [CommRing V]

theorem finiteType_of_fg {k : Type} [CommRing k] [Algebra k V] (hk : Algebra.FiniteType ℤ k) {R : Subalgebra k V}
    (hR : R.FG) : Algebra.FiniteType ℤ R :=
  Algebra.FiniteType.trans hk ((Subalgebra.fg_iff_finiteType R).1 hR)

theorem exists_pairModel {P Q : MorphismProperty Scheme.{0}} [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
    (hQqs : ∀ {A B : Scheme.{0}} {g : A ⟶ B}, Q g → QuasiSeparated g)
    {p : U ⟶ Sp V} (h : HasModel P Q p) (a : T ⟶ U) [IsOpenImmersion a] [CompactSpace T] :
    ∃ (R : Type) (_ : CommRing R) (f : R →+* V), Algebra.FiniteType ℤ R ∧ Nonempty (PairModel P Q (spMap f) p a) := by
  classical
  obtain ⟨k, _, f, X₀, p₀, φ, hk, hPp₀, hQp₀, _, hφ⟩ := h
  have : QuasiSeparated p₀ := hQqs hQp₀
  letI := f.toAlgebra
  have hφ' : IsPullback φ p p₀ (spMap (algebraMap k V)) := hφ
  obtain ⟨s, O, hO, hs⟩ := exists_preimage_eq (bcDiagram p₀ V) (bcCone p₀ V) (isLimitBcCone p₀ V)
    (a ≫ hφ'.isoPullback.hom).opensRange (isCompact_range (Scheme.Hom.continuous _))
  let R := Algebra.adjoin k (s.unop : Set V)
  let O' : (pullback p₀ (spMap (algebraMap k R))).Opens := O
  have hs' : bcMap p₀ R.val ⁻¹ᵁ O' = (a ≫ hφ'.isoPullback.hom).opensRange := hs
  have hO' : CompactSpace O' := isCompact_iff_compactSpace.1 hO
  have : QuasiSeparatedSpace ↥(pullback p₀ (spMap (algebraMap k R))) :=
    (quasiSeparated_iff_quasiSeparatedSpace (pullback.snd p₀ _)).mp inferInstance
  have hqc : QuasiCompact O'.ι := quasiCompact_of_compactSpace _
  have hr : (hφ'.isoPullback.hom ≫ bcMap p₀ R.val) ⁻¹ᵁ O'.ι.opensRange = a.opensRange := by
    rw [Scheme.Opens.opensRange_ι, Scheme.Hom.comp_preimage, hs']
    ext x
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, hφ'.isoPullback.hom.isOpenEmbedding.injective (by simpa using hy)⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by simp⟩
  have hle : Set.range (a ≫ hφ'.isoPullback.hom ≫ bcMap p₀ R.val) ⊆ Set.range O'.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hr.ge ⟨y, rfl⟩
  refine ⟨R, inferInstance, R.val.toRingHom, finiteType_of_fg hk (Subalgebra.fg_adjoin_finset _),
    ⟨⟨_, O', pullback.snd p₀ _, O'.ι, hφ'.isoPullback.hom ≫ bcMap p₀ R.val, IsOpenImmersion.lift O'.ι _ hle,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P) (.of_hasPullback p₀ _) hPp₀,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := Q) (.of_hasPullback p₀ _) hQp₀,
      inferInstance, inferInstance, hqc, ?_, ?_⟩⟩⟩
  · have h₁ : IsPullback hφ'.isoPullback.hom p (pullback.snd _ _) (𝟙 _) := .of_horiz_isIso ⟨by simp⟩
    simpa using h₁.paste_horiz (isPullback_bcMap p₀ R.val)
  · exact IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ _).symm hr

theorem exists_common_level {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (f₁ : R₁ →+* V) (f₂ : R₂ →+* V)
    (h₁ : Algebra.FiniteType ℤ R₁) (h₂ : Algebra.FiniteType ℤ R₂) :
    ∃ (R : Type) (_ : CommRing R) (f : R →+* V) (g₁ : R₁ →+* R) (g₂ : R₂ →+* R), Algebra.FiniteType ℤ R ∧
      spMap f ≫ spMap g₁ = spMap f₁ ∧ spMap f ≫ spMap g₂ = spMap f₂ := by
  let R : Subalgebra ℤ V := f₁.toIntAlgHom.range ⊔ f₂.toIntAlgHom.range
  have hR : R.FG := by
    refine Subalgebra.FG.sup ?_ ?_ <;> rw [← Algebra.map_top]
    · exact h₁.out.map _
    · exact h₂.out.map _
  refine ⟨R, inferInstance, R.val.toRingHom,
    f₁.codRestrict R fun x => (le_sup_left : _ ≤ R) ⟨x, rfl⟩,
    f₂.codRestrict R fun x => (le_sup_right : _ ≤ R) ⟨x, rfl⟩, (Subalgebra.fg_iff_finiteType R).1 hR, ?_, ?_⟩ <;>
  · rw [← Spec.map_comp]
    rfl

theorem hasModel_of_two {P Q : MorphismProperty Scheme.{0}} [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
    [IsZariskiLocalAtSource P]
    (hPlfp : ∀ {A B : Scheme.{0}} {g : A ⟶ B}, P g → LocallyOfFinitePresentation g)
    (hQqs : ∀ {A B : Scheme.{0}} {g : A ⟶ B}, Q g → QuasiSeparated g)
    {X W : Scheme.{0}} (q : X ⟶ Sp V) [QuasiSeparated q] (u : U ⟶ X) (v : W ⟶ X)
    [IsOpenImmersion u] [IsOpenImmersion v] (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v)
    [CompactSpace U] [CompactSpace W] (hU : HasModel P Q (u ≫ q)) (hW : HasModel P Q (v ≫ q))
    (hQspread : ∀ {R : Type} [CommRing R] [Algebra R V], Algebra.FiniteType ℤ R →
      ∀ (X₀ : Scheme.{0}) (q₀ : X₀ ⟶ Sp R) (φ : X ⟶ X₀),
        P q₀ → QuasiCompact q₀ → IsPullback φ q q₀ (spMap (algebraMap R V)) → HasModel P Q q) :
    HasModel P Q q := by
  have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace q).mp inferInstance
  have : CompactSpace ↥(pullback u v) := QuasiCompact.compactSpace_of_compactSpace (pullback.fst u v)
  obtain ⟨R₁, _, f₁, h₁, ⟨M₁⟩⟩ := exists_pairModel hQqs hU (pullback.fst u v)
  obtain ⟨R₂, _, f₂, h₂, ⟨N₁⟩⟩ := exists_pairModel hQqs hW (pullback.snd u v)
  obtain ⟨k, _, f, g₁, g₂, hk, e₁, e₂⟩ := exists_common_level f₁ f₂ h₁ h₂
  letI := f.toAlgebra
  obtain ⟨M⟩ : Nonempty (PairModel P Q (spMap (algebraMap k V)) (u ≫ q) (pullback.fst u v)) := ⟨M₁.baseChange _ _ e₁⟩
  obtain ⟨N⟩ : Nonempty (PairModel P Q (spMap (algebraMap k V)) (v ≫ q) (pullback.snd u v)) := ⟨N₁.baseChange _ _ e₂⟩
  have hN := N.hτ.paste_vert N.hφ
  rw [← pullback.condition_assoc] at hN
  have : LocallyOfFinitePresentation M.p₀ := hPlfp M.hP
  have : LocallyOfFinitePresentation N.p₀ := hPlfp N.hP
  have : QuasiSeparated M.p₀ := hQqs M.hQ
  have : QuasiSeparated N.p₀ := hQqs N.hQ
  obtain ⟨R, e, hR, he, he'⟩ := models_iso (p := M.a₀ ≫ M.p₀) (q := N.a₀ ≫ N.p₀)
    (M.hτ.paste_vert M.hφ) hN
  have w := spMap_algHom_comp R.val
  obtain ⟨X₀, q₀, φ, hPq₀, hqcq₀, hφ⟩ := exists_glued q (IsPullback.of_hasPullback u v) hc
    (M.baseChange _ _ w) (N.baseChange _ _ w) e (by
      apply pullback.hom_ext
      · refine (Category.assoc _ _ _).trans ?_
        exact (he' _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).trans (pullback.lift_fst _ _ _).symm
      · refine (Category.assoc _ _ _).trans ?_
        refine (congrArg _ he).trans ((pullback.lift_snd _ _ _).trans (Eq.trans ?_ (pullback.lift_snd _ _ _).symm))
        simp only [Category.assoc, pullback.condition_assoc])
    (by rw [PairModel.baseChange_a₀_p₀, PairModel.baseChange_a₀_p₀]; exact he)
  exact hQspread (finiteType_of_fg hk hR) X₀ q₀ φ hPq₀ hqcq₀ hφ

theorem hasModel_of_affine (P Q : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
    [IsZariskiLocalAtSource P]
    (hPlfp : ∀ {A B : Scheme.{0}} {g : A ⟶ B}, P g → LocallyOfFinitePresentation g)
    (hQqs : ∀ {A B : Scheme.{0}} {g : A ⟶ B}, Q g → QuasiSeparated g)
    {X : Scheme.{0}} (q : X ⟶ Sp V) [QuasiSeparated q] [QuasiCompact q]
    (hAff : ∀ (U : X.Opens), IsAffine U → HasModel P Q (U.ι ≫ q))
    (hQspread : ∀ (S : X.Opens) {R : Type} [CommRing R] [Algebra R V], Algebra.FiniteType ℤ R →
      ∀ (X₀ : Scheme.{0}) (q₀ : X₀ ⟶ Sp R) (φ : (S : Scheme.{0}) ⟶ X₀),
        P q₀ → QuasiCompact q₀ → IsPullback φ (S.ι ≫ q) q₀ (spMap (algebraMap R V)) →
        HasModel P Q (S.ι ≫ q)) :
    HasModel P Q q := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have key : HasModel P Q ((⊤ : X.Opens).ι ≫ q) := by
    refine compact_open_induction_on (P := fun S => HasModel P Q (S.ι ≫ q)) ⊤ isCompact_univ ?_ ?_
    · exact hAff ⊥ (isAffineOpen_bot X)
    · intro S hS W h
      have : CompactSpace S := isCompact_iff_compactSpace.1 hS
      refine hasModel_of_two hPlfp hQqs _
        (X.homOfLE (le_sup_left : S ≤ S ⊔ W.1)) (X.homOfLE (le_sup_right : W.1 ≤ S ⊔ W.1))
        ?_ ?_ ?_ (hQspread (S ⊔ W.1))
      · rintro ⟨x, hx | hx⟩
        · exact Or.inl ⟨⟨x, hx⟩, Subtype.ext (by simp)⟩
        · exact Or.inr ⟨⟨x, hx⟩, Subtype.ext (by simp)⟩
      · rwa [Scheme.homOfLE_ι_assoc]
      · rw [Scheme.homOfLE_ι_assoc]
        exact hAff W.1 W.2
  obtain ⟨R, _, f, X₀, p₀, φ, h₁, h₂, h₃, h₄, hφ⟩ := key
  refine ⟨R, _, f, X₀, p₀, X.topIso.inv ≫ φ, h₁, h₂, h₃, h₄, ?_⟩
  exact hφ.of_iso X.topIso (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

theorem hasModel_of_isAffine {X : Scheme.{0}} (q : X ⟶ Sp V) [IsAffine X] [LocallyOfFinitePresentation q] :
    HasModel (@LocallyOfFinitePresentation) (@QuasiSeparated) q := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of V) (S := Γ(X, ⊤)) (X.isoSpec.inv ≫ q)
  have h1 : LocallyOfFinitePresentation (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at h1
  let A : Type := Γ(X, ⊤)
  letI : Algebra V A := ψ.hom.toAlgebra
  haveI : Algebra.FinitePresentation V A := h1
  let P := Algebra.Presentation.ofFinitePresentation V A
  let k : Subalgebra ℤ V := Algebra.adjoin ℤ P.coeffs
  have hk : Algebra.FiniteType ℤ k := Algebra.FiniteType.adjoin_of_finite P.finite_coeffs
  haveI : P.HasCoeffs k := ⟨fun x hx => ⟨⟨x, Algebra.subset_adjoin hx⟩, rfl⟩⟩
  let e := P.tensorModelOfHasCoeffsEquiv k
  have h := (CommRingCat.isPushout_tensorProduct k V (P.ModelOfHasCoeffs k)).flip
  have h' : IsPushout (CommRingCat.ofHom (algebraMap k (P.ModelOfHasCoeffs k)))
      (CommRingCat.ofHom (algebraMap k V))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom) ≫ e.toRingEquiv.toCommRingCatIso.hom)
      (CommRingCat.ofHom (algebraMap V A)) := by
    refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · ext x
      exact e.commutes x
  obtain ⟨g, h2⟩ : ∃ g, IsPullback g (Spec.map ψ) (spMap (algebraMap k (P.ModelOfHasCoeffs k)))
      (spMap (algebraMap k V)) := ⟨_, isPullback_SpecMap_of_isPushout _ _ _ _ h'⟩
  refine ⟨k, inferInstance, algebraMap k V, _, spMap (algebraMap k (P.ModelOfHasCoeffs k)), X.isoSpec.hom ≫ g,
    hk, ?_, inferInstance, inferInstance,
    h2.of_iso X.isoSpec.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_⟩
  · exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
      (RingHom.finitePresentation_algebraMap.2 inferInstance)
  · simp
  · simp [hψ]
  · simp
  · simp

theorem hasModel {X : Scheme.{0}} (q : X ⟶ Sp V) [LocallyOfFinitePresentation q] [QuasiSeparated q]
    [QuasiCompact q] : HasModel (@LocallyOfFinitePresentation) (@QuasiSeparated) q := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{0})
    (Q := @RingHom.FinitePresentation)
  refine hasModel_of_affine (@LocallyOfFinitePresentation) (@QuasiSeparated) (fun h => h) (fun h => h) q
    (fun U _ => hasModel_of_isAffine (U.ι ≫ q)) fun S R _ _ hR X₀ q₀ φ hPq₀ hqcq₀ hφ => ?_
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian q₀
  exact ⟨R, inferInstance, algebraMap R V, X₀, q₀, φ, hR, hPq₀,
    (quasiSeparated_iff_quasiSeparatedSpace q₀).mpr inferInstance, hqcq₀, hφ⟩

end GlobalTheory.SpreadScheme
