module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFlatFibresDvr
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RingHomFlatCodescendsAlongFaithfullyFlat
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open TensorProduct
open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace FiniteFibreFlat

open TensorProduct IsLocalRing

section Algebra

theorem lTensor_map_injective {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    (p : Ideal R) :
    Function.Injective ((p.map (algebraMap R A)).subtype.lTensor M) := by
  let I := p.map (algebraMap R A)
  let c : p →ₗ[R] I :=
    { toFun := fun r => ⟨algebraMap R A r, Ideal.mem_map_of_mem _ r.2⟩
      map_add' := fun r s => Subtype.ext (by simp)
      map_smul' := fun r s => Subtype.ext (by simp [Algebra.smul_def]) }
  let φ : M ⊗[R] p →ₗ[R] M ⊗[A] I :=
    TensorProduct.mapOfCompatibleSMul A R R M I ∘ₗ c.lTensor M
  have hφ : ∀ m r, φ (m ⊗ₜ r) = m ⊗ₜ[A] c r := fun _ _ => rfl
  have hsurj : ∀ x, x ∈ LinearMap.range φ := by
    intro x
    induction x with
    | add a b ha hb => exact add_mem ha hb
    | tmul m i =>
      obtain ⟨i, hi⟩ := i
      induction hi using Submodule.span_induction generalizing m with
      | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := hx
        exact ⟨m ⊗ₜ ⟨r, hr⟩, rfl⟩
      | zero =>
        change m ⊗ₜ[A] (0 : I) ∈ _
        rw [tmul_zero]
        exact zero_mem _
      | add x y hx hy ihx ihy =>
        change m ⊗ₜ[A] ((⟨x, hx⟩ : I) + ⟨y, hy⟩) ∈ _
        rw [tmul_add]
        exact add_mem (ihx m) (ihy m)
      | smul a x hx ih =>
        change m ⊗ₜ[A] (a • (⟨x, hx⟩ : I)) ∈ _
        rw [← smul_tmul]
        exact ih _
  have hcomp : ∀ y, TensorProduct.rid A M (I.subtype.lTensor M (φ y)) =
      TensorProduct.rid R M (p.subtype.lTensor M y) := by
    intro y
    induction y with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul m r => simp [hφ, c]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  have h0 := hcomp y
  rw [hx, map_zero, eq_comm, map_eq_zero_iff _ (TensorProduct.rid R M).injective,
    map_eq_zero_iff _ (Module.Flat.lTensor_preserves_injective_linearMap p.subtype
      p.injective_subtype)] at h0
  rw [h0, map_zero]

end Algebra

open FibreFlat

variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y}

theorem flatOver_of_comp_base {S₀ : Scheme.{0}} {g : Y ⟶ S₀} {u : S₀ ⟶ S} {t : S' ⟶ S₀}
    (H : FlatOver f (g ≫ u) (t ≫ u)) : FlatOver f g t :=
  fun _ _ a b j h sq e => H a b j h sq (by rw [← Category.assoc, e, Category.assoc])

theorem flatOver_descend {S'' : Scheme.{0}} {g : Y ⟶ S} {t : S' ⟶ S} (σ : S'' ⟶ S')
    [Surjective σ] [Flat σ] [QuasiCompact σ] (H : FlatOver f g (σ ≫ t)) : FlatOver f g t := by
  intro W Z a b j h sq e
  have := flat_descendsAlong_fpqc
  have sq1 := IsPullback.of_hasPullback b (pullback.fst h σ)
  have h1 : Flat (pullback.snd b (pullback.fst h σ)) :=
    H _ _ _ (pullback.snd h σ) (sq1.paste_horiz sq)
      (by rw [Category.assoc, e, ← Category.assoc, pullback.condition, Category.assoc])
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq1.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h1

end FiniteFibreFlat

namespace FinitePresFibreFlat

open TensorProduct IsLocalRing FiniteFibreFlat

section Algebra

theorem free_of_flat_reduction {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    [Module.FinitePresentation A M] (p : Ideal R) (hp : p.map (algebraMap R A) ≤ maximalIdeal A)
    [Module.Flat (A ⧸ p.map (algebraMap R A)) ((A ⧸ p.map (algebraMap R A)) ⊗[A] M)] :
    Module.Free A M := by
  set I := p.map (algebraMap R A) with hI
  have hrel : LocalFlat.RelationsLift I M :=
    LocalFlat.relationsLift_of_flat (C := A ⧸ I) Ideal.Quotient.mk_surjective Ideal.mk_ker
      (TensorProduct.mk A (A ⧸ I) M 1) (TensorProduct.mk_surjective A M (A ⧸ I)
        Ideal.Quotient.mk_surjective) (LinearMap.ker_tensorProductMk M)
  apply Module.free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hrel (maximalIdeal A) (maximalIdeal A).subtype x (by rw [hx]; simp)
  let e := Submodule.comapSubtypeEquivOfLe hp
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ (lTensor_map_injective p)] at hy
  have : y = 0 := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [this, map_zero]

theorem flat_of_flat_fibres {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Module.FinitePresentation A B]
    [Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) :
    Module.Flat A B := by
  refine Module.flat_of_isLocalized_maximal A B (fun P _ => Localization.AtPrime P ⊗[A] B)
    (fun P _ => TensorProduct.mk A (Localization.AtPrime P) B 1) fun P _ => ?_
  let A' := Localization.AtPrime P
  let p : Ideal R := (maximalIdeal A').comap (algebraMap R A')
  let I := p.map (algebraMap R A')
  have h1 : Module.Flat R (B ⊗[A] A') := Module.Flat.trans R B (B ⊗[A] A')
  have h2 : Module.Flat R (A' ⊗[A] B) :=
    Module.Flat.of_linearEquiv
      ((Algebra.TensorProduct.comm A A' B).restrictScalars R).toLinearEquiv
  have h3 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A] B) := by
    let ψ : R →+* A' ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R A')
    have hψ₁ : p ≤ RingHom.ker ψ := fun r hr =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    have hψ₂ : p.primeCompl ≤ (IsUnit.submonoid (A' ⧸ I)).comap ψ := by
      intro r hr
      have : IsUnit (algebraMap R A' r) := by
        by_contra h
        exact hr h
      exact this.map (Ideal.Quotient.mk I)
    refine H p.ResidueField (A' ⧸ I) (algebraMap R _) (Ideal.ResidueField.lift p ψ hψ₁ hψ₂) ?_
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p ψ hψ₁ hψ₂ r).symm
  have h4 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A'] (A' ⊗[A] B)) :=
    Module.Flat.of_linearEquiv
      (AlgebraTensorModule.cancelBaseChange A A' (A' ⧸ I) (A' ⧸ I) B)
  have h5 : Module.Free A' (A' ⊗[A] B) :=
    free_of_flat_reduction p Ideal.map_comap_le
  have h6 : Module.Flat A' (A' ⊗[A] B) := Module.Flat.of_free
  exact Module.Flat.trans A A' (A' ⊗[A] B)

end Algebra

end FinitePresFibreFlat

namespace QuasiFiniteFibreFlat

theorem flat_baseChange_trans (S C T D : Type) [CommRing S] [CommRing C] [CommRing T] [CommRing D]
    [Algebra S C] [Algebra S T] [Algebra S D] [Algebra T D] [IsScalarTower S T D]
    [Module.Flat T D] [h : Module.Flat C (C ⊗[S] T)] : Module.Flat C (C ⊗[S] D) := by
  let l := IsScalarTower.toAlgHom S T D
  have hl : (l : T →+* D).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have h1 := (RingHom.flat_algebraMap_iff.mpr h).comp (RingHom.Flat.lTensor (S := S) C hl)
  rw [← RingHom.flat_algebraMap_iff]
  convert h1 using 1
  ext c
  simp

theorem flat_away {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.FinitePresentation A B]
    [hRB : Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B))
    (A' : Type) [CommRing A'] [Algebra A A'] [Module.Flat A A'] (e : A' ⊗[A] B)
    [Module.Finite A' (Localization.Away e)] : Module.Flat A' (Localization.Away e) := by
  let D := Localization.Away e
  letI : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Flat (A' ⊗[A] B) D := IsLocalization.flat _ (Submonoid.powers e)
  haveI : Algebra.FinitePresentation (A' ⊗[A] B) D := IsLocalization.Away.finitePresentation e
  haveI : Algebra.FinitePresentation A' D := .trans A' (A' ⊗[A] B) D
  haveI : Module.FinitePresentation A' D :=
    Module.FinitePresentation.of_finite_of_finitePresentation A' D
  haveI : Module.Flat R D := by
    have h1 : (algebraMap B (B ⊗[A] A')).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
    have h2 := h1.comp (g := (Algebra.TensorProduct.comm A B A' : B ⊗[A] A' →+* A' ⊗[A] B))
          (.of_bijective (Algebra.TensorProduct.comm A B A').bijective)
    have h3 := ((RingHom.flat_algebraMap_iff.mpr hRB).comp h2).comp
      (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (A' ⊗[A] B) D))
    rw [← RingHom.flat_algebraMap_iff]
    convert h3 using 1
    ext r
    rw [IsScalarTower.algebraMap_apply R A' D]
    change algebraMap A' D (algebraMap A A' (algebraMap R A r)) =
      algebraMap (A' ⊗[A] B) D (1 ⊗ₜ algebraMap R B r)
    rw [IsScalarTower.algebraMap_apply A' (A' ⊗[A] B) D, IsScalarTower.algebraMap_apply R A B,
      Algebra.TensorProduct.algebraMap_apply]
    congr 1
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul _
  refine FinitePresFibreFlat.flat_of_flat_fibres (R := R) (A := A') (B := D)
    fun k C _ _ _ t h w => ?_
  letI : Algebra A C := ((algebraMap A' C).comp (algebraMap A A')).toAlgebra
  haveI : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq' rfl
  haveI := H k C t h w
  haveI : Module.Flat C (C ⊗[A'] (A' ⊗[A] B)) :=
    Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange A A' C C B)
  exact flat_baseChange_trans A' C (A' ⊗[A] B) D

end QuasiFiniteFibreFlat

theorem flat_of_quasiFinite_of_flat_fibres :
    ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.FinitePresentation A B] [Algebra.QuasiFinite A B] [Module.Flat R B], (∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C), (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) → Module.Flat A B := by
  intro R A B _ _ _ _ _ _ _ _ _ _ H
  refine Module.flat_of_isLocalized_maximal B B (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap B _) fun Q _ => ?_
  obtain ⟨A', _, _, _, P, _, _, e, -, Q', _, _, hQ, he, -, hfin, -⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (Q.under A) Q
  let T := A' ⊗[A] B
  let D := Localization.Away e
  have hD : Module.Flat A' D := QuasiFiniteFibreFlat.flat_away H A' e
  let i : B →+* T := Algebra.TensorProduct.includeRight.toRingHom
  have hi : i.Flat := by
    have h1 : (algebraMap B (B ⊗[A] A')).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
    exact h1.comp (g := (Algebra.TensorProduct.comm A B A' : B ⊗[A] A' →+* A' ⊗[A] B))
          (.of_bijective (Algebra.TensorProduct.comm A B A').bijective)
  let β := Localization.localRingHom Q Q' i hQ.symm
  have hβ : β.Flat := RingHom.Flat.localRingHom hi Q' Q hQ.symm
  have hle : Submonoid.powers e ≤ Q'.primeCompl := by
    rw [Submonoid.powers_le]; exact he
  letI : Algebra D (Localization.AtPrime Q') :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  haveI : IsScalarTower T D (Localization.AtPrime Q') :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  haveI := IsLocalization.isLocalization_of_submonoid_le D (Localization.AtPrime Q') _ _ hle
  have hDQ : Module.Flat D (Localization.AtPrime Q') :=
    IsLocalization.flat _ (Q'.primeCompl.map (algebraMap T D))
  rw [← RingHom.flat_algebraMap_iff]
  refine ringHom_flat_of_square_of_isLocalHom (α := algebraMap A A') (β := β)
    (φ' := (algebraMap D (Localization.AtPrime Q')).comp (algebraMap A' D)) ?_
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hβ
    ((RingHom.flat_algebraMap_iff.mpr hD).comp (RingHom.flat_algebraMap_iff.mpr hDQ))
  ext a
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q), Localization.localRingHom_to_map,
    IsScalarTower.algebraMap_apply A' T D, ← IsScalarTower.algebraMap_apply T D]
  congr 1
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul a

end GlobalTheory

namespace PositivityTheory.HtPt.Twhopf

open GlobalTheory.FibreFlat in
set_option backward.isDefEq.respectTransparency false in
theorem flat_of_flatOver_fields {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hY : LocallyOfFinitePresentation g) (h0 : LocallyOfFinitePresentation (f ≫ g))
    (h1 : Flat (f ≫ g)) (h2 : LocallyQuasiFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    refine this (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      inferInstance (MorphismProperty.of_isPullback (sq.paste_vert sq') h0)
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1)
      (MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) sq h2)
      (fun k _ t => ?_) ⟨_, rfl⟩
    intro W Z a b j h sq2 e
    refine ((H k (t ≫ u)).target sq) a b j h sq2 ?_
    rw [pullback.condition, reassoc_of% e]
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i))
      (MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) sq h2) (Y.affineCover.f i ≫ g)
      inferInstance (by rw [e]; infer_instance) (by rw [e]; infer_instance)
      (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X
  · refine IsZariskiLocalAtSource.of_openCover X.affineCover fun i => ?_
    exact this (X.affineCover.f i ≫ f) inferInstance (by rw [Category.assoc]; infer_instance)
      (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1 h0
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)] at h2
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hY h0
  let : Algebra R A := g.hom.toAlgebra
  let : Algebra A B := f.hom.toAlgebra
  let : Algebra R B := (g ≫ f).hom.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat R B := h1
  have : Algebra.QuasiFinite A B := h2
  have : Algebra.FinitePresentation R A := hY
  have : Algebra.FinitePresentation R B := h0
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A B
  refine GlobalTheory.flat_of_quasiFinite_of_flat_fibres R A B fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this

end PositivityTheory.HtPt.Twhopf
