module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularLocalDomain
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.IrreducibleComponents

/-! # Restricting finite étale correspondences to clopen subschemes

A clopen part of the generic fibre extends over a smooth scheme over a regular domain.
On the resulting clopen cover, restriction preserves the degrees and point identities
of the correspondences. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory.GalV (HTower Splits)

namespace UpperTheory.Gal.Int.Geo.Cut

structure Part {Y' Y : Scheme.{0}} (j : Y' ⟶ Y) : Prop where
  op : IsOpenImmersion j
  cl : IsClosed (Set.range j)

structure Res {Y' Y T' T : Scheme.{0}} (j : Y' ⟶ Y) (s t : T ⟶ Y) (i : T' ⟶ T) (s' t' : T' ⟶ Y') : Prop where
  op : IsOpenImmersion i
  rng : Set.range i = s ⁻¹' Set.range j ∩ t ⁻¹' Set.range j
  es : s' ≫ j = i ≫ s
  et : t' ≫ j = i ≫ t

theorem genDense (O : Type) [CommRing O] [IsDomain O] (Y : Scheme) (p : Y ⟶ Spec (CommRingCat.of O))
    (hp : Flat p) : Dense {y : Y | (p y).asIdeal = ⊥} := by
  have hg : GeneralizingMap p := Flat.generalizingMap p
  rw [dense_iff_inter_open]
  rintro U hU ⟨y, hy⟩
  let η : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : η ⤳ p y := (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y', hy', hpy'⟩ := hg hη
  exact ⟨y', hy'.mem_open hU hy, by simp only [Set.mem_ofPred_eq, hpy', η]⟩

theorem genRange (O k : Type) [CommRing O] [IsDomain O] [Field k] [Algebra O k] [IsFractionRing O k]
    (Y : Scheme) (p : Y ⟶ Spec (CommRingCat.of O)) :
    Set.range (pullback.fst p (gen O k)) = {y : Y | (p y).asIdeal = ⊥} ∧
      Topology.IsEmbedding (pullback.fst p (gen O k)) := by
  have : IsPreimmersion (gen O k) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have hker : RingHom.ker (algebraMap O k) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O k)
  refine ⟨?_, (pullback.fst p (gen O k)).isEmbedding⟩
  rw [Scheme.Pullback.range_fst]
  ext y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, hz⟩
    rw [← hz]
    change Ideal.comap (algebraMap O k) (z : PrimeSpectrum k).asIdeal = ⊥
    have : (z : PrimeSpectrum k).asIdeal.IsPrime := (z : PrimeSpectrum k).isPrime
    rw [Ideal.eq_bot_of_prime (z : PrimeSpectrum k).asIdeal, ← RingHom.ker_eq_comap_bot, hker]
  · intro h
    refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap O k) ⊥ = (p y).asIdeal
    rw [h, ← RingHom.ker_eq_comap_bot, hker]

theorem stalkDom (O : Type) [CommRing O] [IsRegularRing O] (Y : Scheme) (p : Y ⟶ Spec (CommRingCat.of O))
    (hp : Smooth p) (y : Y) : IsDomain (Y.presheaf.stalk y) := by
  have := GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth p y
  exact GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain

private theorem exists_isClopen_preimage {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]
    (f : P → X) (hf : Topology.IsEmbedding f) (hd : Dense (Set.range f))
    (hl : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ IsPreirreducible W)
    (U : Set P) (hU : IsClopen U) : ∃ V : Set X, IsClopen V ∧ f ⁻¹' V = U := by
  have key : ∀ W : Set X, IsOpen W → IsPreirreducible W → (f ⁻¹' W ⊆ U ∨ f ⁻¹' W ⊆ Uᶜ) := by
    intro W hW hWi
    obtain ⟨A, hA, hAU⟩ := hf.isInducing.isOpen_iff.mp hU.isOpen
    obtain ⟨B, hB, hBU⟩ := hf.isInducing.isOpen_iff.mp hU.compl.isOpen
    by_contra hc
    rw [not_or, Set.not_subset, Set.not_subset] at hc
    obtain ⟨⟨a, ha, haU⟩, ⟨b, hb, hbU⟩⟩ := hc
    have h1 : (W ∩ A).Nonempty := by
      refine ⟨f b, hb, ?_⟩
      rw [← Set.mem_preimage, hAU]
      simpa using hbU
    have h2 : (W ∩ B).Nonempty := by
      refine ⟨f a, ha, ?_⟩
      rw [← Set.mem_preimage, hBU]
      exact haU
    obtain ⟨x, hxW, hxA, hxB⟩ := hWi A B hA hB h1 h2
    obtain ⟨_, ⟨q, rfl⟩, -, hqA, hqB⟩ := hd.exists_mem_open (hW.inter (hA.inter hB)) ⟨x, hxW, hxA, hxB⟩
    have hq1 : q ∈ U := by rw [← hAU]; exact hqA
    have hq2 : q ∈ Uᶜ := by rw [← hBU]; exact hqB
    exact hq2 hq1
  refine ⟨{x | ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ IsPreirreducible W ∧ f ⁻¹' W ⊆ U}, ⟨?_, ?_⟩, ?_⟩
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨W, hW, hxW, hWi⟩ := hl x
    have hWc : f ⁻¹' W ⊆ Uᶜ := by
      rcases key W hW hWi with h | h
      · exact absurd ⟨W, hW, hxW, hWi, h⟩ hx
      · exact h
    refine ⟨W, ?_, hW, hxW⟩
    rintro z hz ⟨W', hW', hzW', hW'i, hW'U⟩
    obtain ⟨_, ⟨q, rfl⟩, hqW, hqW'⟩ := hd.exists_mem_open (hW.inter hW') ⟨z, hz, hzW'⟩
    exact hWc hqW (hW'U hqW')
  · rw [isOpen_iff_forall_mem_open]
    rintro x ⟨W, hW, hxW, hWi, hWU⟩
    exact ⟨W, fun z hz => ⟨W, hW, hz, hWi, hWU⟩, hW, hxW⟩
  · ext q
    constructor
    · rintro ⟨W, -, hqW, -, hWU⟩
      exact hWU hqW
    · intro hq
      obtain ⟨W, hW, hxW, hWi⟩ := hl (f q)
      rcases key W hW hWi with h | h
      · exact ⟨W, hW, hxW, hWi, h⟩
      · exact absurd hq (h hxW)

private theorem exists_isPreirreducible_nhd (Y : Scheme.{0}) [IsLocallyNoetherian Y]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y)) (y : Y) :
    ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ IsPreirreducible W := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hN : TopologicalSpace.NoetherianSpace (U : Scheme) := noetherianSpace_of_isAffineOpen U hU
  have hdom : ∀ z : (U : Scheme), IsDomain ((U : Scheme).presheaf.stalk z) := by
    intro z
    have e := (Scheme.Opens.stalkIso U z).commRingCatIsoToRingEquiv
    have := hY z.1
    exact Function.Injective.isDomain e.toRingHom e.injective
  let z : (U : Scheme) := ⟨y, hyU⟩
  have hC : IsOpen (irreducibleComponent z) := by
    have h := FunctorialResolution.EmbeddedResolution.isOpen_sUnion_of_subset_irreducibleComponents
      (X := (U : Scheme)) (𝒜 := {irreducibleComponent z}) ?_ ?_
    · rwa [Set.sUnion_singleton] at h
    · rintro C₁ h1 C₂ h2 ⟨x, hx1, hx2⟩
      exact FunctorialResolution.EmbeddedResolution.irreducibleComponents_eq_of_stalk_isDomain
        (U : Scheme) hdom h1 h2 hx1 hx2
    · intro D hD
      rw [Set.mem_singleton_iff.mp hD]
      exact irreducibleComponent_mem_irreducibleComponents _
  refine ⟨U.ι '' irreducibleComponent z, U.ι.isOpenEmbedding.isOpenMap _ hC,
    ⟨z, mem_irreducibleComponent, rfl⟩, ?_⟩
  exact isIrreducible_irreducibleComponent.isPreirreducible.image _ U.ι.continuous.continuousOn

theorem clopenExt (O k : Type) [CommRing O] [IsDomain O] [IsRegularRing O] [Field k] [Algebra O k]
    [IsFractionRing O k] (Y : Scheme) (p : Y ⟶ Spec (CommRingCat.of O)) (hp : Smooth p)
    (U : Set ↥(pullback p (gen O k))) (hU : IsClopen U) :
    ∃ V : Y.Opens, IsClosed (V : Set Y) ∧ pullback.fst p (gen O k) ⁻¹' V = U := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨hr, he⟩ := genRange O k Y p
  obtain ⟨V, hV, hVU⟩ := exists_isClopen_preimage (pullback.fst p (gen O k)) he
    (by rw [hr]; exact genDense O Y p inferInstance)
    (exists_isPreirreducible_nhd Y (stalkDom O Y p hp)) U hU
  exact ⟨⟨V, hV.isOpen⟩, hV.isClosed, hVU⟩

private theorem range_subset_range_of_comp_eq_of_ne_zero {l : ℕ} {Y' Y Z' : Scheme}
    {j : Y' ⟶ Y} (hP : Part j) {T : crystallineComparison.Corr l Y}
    {i : Z' ⟶ T.Z} {s' t' : Z' ⟶ Y'} (hR : Res j T.p T.r i s' t')
    (hr : ∀ x : T.Z, T.p x ∈ Set.range j → T.p x ∈ Y.basicOpen (l : Γ(Y, ⊤)) → T.r x ∈ Set.range j)
    {V : Type} [CommRing V] [IsDomain V] (hl : (l : V) ≠ 0) {y' : Spec (CommRingCat.of V) ⟶ Y'}
    (z : Spec (CommRingCat.of V) ⟶ T.Z) (hz : z ≫ T.p = y' ≫ j) :
    Set.range z ⊆ Set.range i := by
  have hp : ∀ s, T.p (z s) = j (y' s) := fun s => by
    rw [← Scheme.Hom.comp_apply, hz, Scheme.Hom.comp_apply]
  let η : Spec (CommRingCat.of V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)
  have hη : T.p (z η) ∈ Y.basicOpen (l : Γ(Y, ⊤)) := by
    rw [← Scheme.Hom.comp_apply, ← SetLike.mem_coe, ← Set.mem_preimage, ← Scheme.Hom.coe_preimage,
      Scheme.preimage_basicOpen_top, map_natCast, basicOpen_eq_of_affine', map_natCast]
    exact hl
  have hrη : T.r (z η) ∈ Set.range j := hr _ (by rw [hp]; exact ⟨_, rfl⟩) hη
  rintro _ ⟨s, rfl⟩
  have hsp : η ⤳ s := (PrimeSpectrum.le_iff_specializes (R := V) _ _).1 bot_le
  have hrs : T.r (z s) ∈ Set.range j :=
    ((hsp.map z.continuous).map T.r.continuous).mem_closed hP.cl hrη
  rw [hR.rng]
  exact ⟨by rw [Set.mem_preimage, hp]; exact ⟨_, rfl⟩, hrs⟩

/-- Composition with the clopen immersion identifies the sections over a point and its image. -/
private noncomputable def secEquiv {l : ℕ} {Y' Y Z' : Scheme} {j : Y' ⟶ Y} (hP : Part j)
    {T : crystallineComparison.Corr l Y} {i : Z' ⟶ T.Z} {s' t' : Z' ⟶ Y'} (hR : Res j T.p T.r i s' t')
    (hr : ∀ x : T.Z, T.p x ∈ Set.range j → T.p x ∈ Y.basicOpen (l : Γ(Y, ⊤)) → T.r x ∈ Set.range j)
    {V : Type} [CommRing V] [IsDomain V] (hl : (l : V) ≠ 0) (y' : Spec (CommRingCat.of V) ⟶ Y') :
    {z : Spec (CommRingCat.of V) ⟶ Z' // z ≫ s' = y'} ≃ T.Sec (y' ≫ j) := by
  have := hP.op
  have := hR.op
  exact
    { toFun := fun z => ⟨z.1 ≫ i, by rw [Category.assoc, ← hR.es, ← Category.assoc, z.2]⟩
      invFun := fun w => ⟨IsOpenImmersion.lift i w.1 (range_subset_range_of_comp_eq_of_ne_zero hP hR hr hl w.1 w.2), by
        rw [← cancel_mono j, Category.assoc, hR.es, ← Category.assoc, IsOpenImmersion.lift_fac, w.2]⟩
      left_inv := fun z => Subtype.ext ((cancel_mono i).mp (IsOpenImmersion.lift_fac _ _ _))
      right_inv := fun w => Subtype.ext (IsOpenImmersion.lift_fac _ _ _) }

theorem corrCut (l : ℕ) (Y' Y T' : Scheme.{0}) (j : Y' ⟶ Y) (T : crystallineComparison.Corr l Y)
    (i : T' ⟶ T.Z) (s' t' : T' ⟶ Y') (hj : Part j) (hr : Res j T.p T.r i s' t')
    (hcond : ∀ x : T.Z, T.p x ∈ Set.range j → T.p x ∈ Y.basicOpen (l : Γ(Y, ⊤)) → T.r x ∈ Set.range j) :
    IsFinite s' ∧ Etale (s' ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K], (l : K) ≠ 0 → ∀ y : Spec (CommRingCat.of K) ⟶ Y',
        Nat.card {z : Spec (CommRingCat.of K) ⟶ T' // z ≫ s' = y} = T.d := by
  have := hj.op
  have := hr.op
  have hcl : IsClosed (Set.range i) := by
    rw [hr.rng]
    exact (hj.cl.preimage T.p.continuous).inter (hj.cl.preimage T.r.continuous)
  have : IsClosedImmersion i := .of_isPreimmersion _ hcl
  have := T.fin
  have : IsFinite (s' ≫ j) := by rw [hr.es]; infer_instance
  refine ⟨IsFinite.of_comp s' j, ?_, ?_⟩
  · have hV : j ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) = Y'.basicOpen (l : Γ(Y', ⊤)) := by
      rw [Scheme.Hom.preimage_basicOpen, map_natCast]
      rfl
    let a := (s' ⁻¹ᵁ Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ i
    have ha : Set.range a ⊆ Set.range (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      rintro _ ⟨u, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hu : s' ((s' ⁻¹ᵁ Y'.basicOpen (l : Γ(Y', ⊤))).ι u) ∈ j ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) := by
        rw [hV]
        exact u.2
      change T.p (i ((s' ⁻¹ᵁ Y'.basicOpen (l : Γ(Y', ⊤))).ι u)) ∈ Y.basicOpen (l : Γ(Y, ⊤))
      rw [← Scheme.Hom.comp_apply, ← hr.es, Scheme.Hom.comp_apply]
      exact hu
    have : Etale (IsOpenImmersion.lift _ a ha ≫ (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι) := by
      rw [IsOpenImmersion.lift_fac]
      infer_instance
    have : Etale (IsOpenImmersion.lift _ a ha) := Etale.of_comp _ (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι
    have := T.et
    have e1 : (s' ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) ≫ (Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ j =
        IsOpenImmersion.lift _ a ha ≫ (T.p ∣_ Y.basicOpen (l : Γ(Y, ⊤))) ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      rw [morphismRestrict_ι, ← Category.assoc (IsOpenImmersion.lift _ a ha), IsOpenImmersion.lift_fac,
        ← Category.assoc, morphismRestrict_ι, Category.assoc, hr.es]
      simp only [a, Category.assoc]
    have : Etale ((s' ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) ≫ (Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ j) := by
      rw [e1]
      infer_instance
    exact Etale.of_comp _ ((Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ j)
  · intro K _ _ hl y
    exact (Nat.card_congr (secEquiv hj hr hcond hl y)).trans (T.deg K hl (y ≫ j))

private theorem splits_cancel {A B Z : Scheme.{0}} (m : A ⟶ B) [Mono m] (f : Z ⟶ A) {J : Type}
    (a : J → (Z ⟶ Z)) (h : Splits (f ≫ m) (f ≫ m) a) : Splits f f a := by
  obtain ⟨h, hi⟩ := h
  have h' : ∀ j, a j ≫ f = f := fun j =>
    (cancel_mono m).1 (by rw [Category.assoc]; exact h j)
  refine ⟨h', ?_⟩
  let e : pullback f f ⟶ pullback (f ≫ m) (f ≫ m) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition_assoc])
  let e' : pullback (f ≫ m) (f ≫ m) ⟶ pullback f f :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _)
      (by rw [← cancel_mono m, Category.assoc, Category.assoc, pullback.condition])
  have : IsIso e := ⟨⟨e', by
    apply pullback.hom_ext
    · simp only [e, e', Category.assoc, Category.id_comp]
      repeat' rw [pullback.lift_fst]
    · simp only [e, e', Category.assoc, Category.id_comp]
      repeat' rw [pullback.lift_snd], by
    apply pullback.hom_ext
    · simp only [e, e', Category.assoc, Category.id_comp]
      repeat' rw [pullback.lift_fst]
    · simp only [e, e', Category.assoc, Category.id_comp]
      repeat' rw [pullback.lift_snd]⟩⟩
  have heq : (Limits.Sigma.desc fun j => pullback.lift (a j) (𝟙 Z) (by simp [h' j]) :
      (∐ fun _ : J => Z) ⟶ pullback f f) ≫ e =
      Limits.Sigma.desc fun j => pullback.lift (a j) (𝟙 Z) (by simp [h j]) := by
    apply Limits.Sigma.hom_ext
    intro j
    simp only [Limits.colimit.ι_desc_assoc, Limits.colimit.ι_desc, Limits.Cofan.mk_ι_app]
    apply pullback.hom_ext
    · simp only [e, Category.assoc]
      repeat' rw [pullback.lift_fst]
    · simp only [e, Category.assoc]
      repeat' rw [pullback.lift_snd]
  have : IsIso ((Limits.Sigma.desc fun j => pullback.lift (a j) (𝟙 Z) (by simp [h' j]) :
      (∐ fun _ : J => Z) ⟶ pullback f f) ≫ e) := by
    rw [heq]
    exact hi
  exact IsIso.of_isIso_comp_right _ e

theorem coverCut (k L O : Type) [Field k] [Field L] [CommRing O] [Algebra O k] (H : HTower k)
    (θ : H.Γ → L) (C : Cover H θ O) (V : C.Y.Opens) (hVcl : IsClosed (V : Set C.Y))
    (hpre : pullback.fst C.p (gen O k) ⁻¹' V = Set.range (pullback.lift C.π H.q C.ov)) :
    ∃ (C' : Cover H θ O) (j : C'.Y ⟶ C.Y),
      Part j ∧ Set.range j = V ∧ C'.p = j ≫ C.p ∧ C'.π ≫ j = C.π ∧ C'.Onto := by
  have hV : ∀ z, C.π z ∈ V := by
    intro z
    have hz : pullback.lift C.π H.q C.ov z ∈
        ⇑(pullback.fst C.p (gen O k)) ⁻¹' (V : Set C.Y) := by
      rw [hpre]
      exact ⟨z, rfl⟩
    simpa only [Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst,
      SetLike.mem_coe] using hz
  have hrange : Set.range ⇑C.π ⊆ Set.range ⇑V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hV z
  let π' : H.Z ⟶ V.toScheme := IsOpenImmersion.lift V.ι C.π hrange
  have hπ' : π' ≫ V.ι = C.π := IsOpenImmersion.lift_fac V.ι C.π hrange
  have ov' : π' ≫ (V.ι ≫ C.p) = H.q ≫ gen O k := by
    rw [← Category.assoc, hπ']
    exact C.ov
  let m : pullback (V.ι ≫ C.p) (gen O k) ⟶ pullback C.p (gen O k) :=
    pullback.lift (pullback.fst _ _ ≫ V.ι) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition)
  have hsq : IsPullback (pullback.fst (V.ι ≫ C.p) (gen O k)) m V.ι
      (pullback.fst C.p (gen O k)) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd C.p (gen O k)) (v₂₂ := C.p)
      (h₃₁ := gen O k) ?_ ?_ (IsPullback.of_hasPullback C.p (gen O k))
    · rw [pullback.lift_snd]
      exact IsPullback.of_hasPullback (V.ι ≫ C.p) (gen O k)
    · rw [pullback.lift_fst]
  have hmo : IsOpenImmersion m :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) hsq
      (inferInstanceAs (IsOpenImmersion V.ι))
  let L' : H.Z ⟶ pullback (V.ι ≫ C.p) (gen O k) := pullback.lift π' H.q ov'
  have hLm : L' ≫ m = pullback.lift C.π H.q C.ov := by
    apply pullback.hom_ext
    · simp only [L', m, Category.assoc]
      rw [pullback.lift_fst, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hπ']
    · simp only [L', m, Category.assoc]
      rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]
  have : Smooth C.p := C.smooth
  have : IsClosedImmersion V.ι :=
    .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hVcl)
  have hfin : IsFinite (L' ≫ m) := by
    rw [hLm]
    exact C.finπ
  have het : Etale (L' ≫ m) := by
    rw [hLm]
    exact C.etπ
  have spl' : GlobalTheory.GalV.Splits L' L' C.a := by
    apply splits_cancel m L' C.a
    rw [hLm]
    exact C.spl
  have hproj : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (V.ι ≫ C.p) := by
    obtain ⟨N, i, hi, hic⟩ := C.proj
    have := hi
    exact ⟨N, V.ι ≫ i, inferInstance, by rw [Category.assoc, hic]⟩
  have hdim : ∃ d, SmoothOfRelativeDimension d (V.ι ≫ C.p) := by
    obtain ⟨d, hd⟩ := C.dim
    exact ⟨d, HasRingHomProperty.comp_of_isOpenImmersion
      (P := @SmoothOfRelativeDimension d) _ _ hd⟩
  have honto : AlgebraicGeometry.Surjective L' := by
    refine ⟨fun w => ?_⟩
    have hw : m w ∈ ⇑(pullback.fst C.p (gen O k)) ⁻¹' (V : Set C.Y) := by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]
      simp only [m, pullback.lift_fst]
      apply (show Set.range ⇑V.ι ⊆ (V : Set C.Y) by rw [Scheme.Opens.range_ι])
      exact ⟨_, rfl⟩
    rw [hpre] at hw
    obtain ⟨z, hz⟩ := hw
    refine ⟨z, m.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hLm, hz]
  exact ⟨Cover.mk V.toScheme (V.ι ≫ C.p) inferInstance hproj π' ov' C.Δ (grp := C.grp)
      (fin := C.fin) C.a (IsFinite.of_comp L' m) (Etale.of_comp L' m) C.one C.mul spl'
      C.fix hdim,
    V.ι, ⟨inferInstance, by rw [Scheme.Opens.range_ι]; exact hVcl⟩,
    Scheme.Opens.range_ι V, rfl, hπ', honto⟩

theorem fEtCut (Y' Y T' T : Scheme.{0}) (j : Y' ⟶ Y) (s t : T ⟶ Y) (i : T' ⟶ T)
    (s' t' : T' ⟶ Y') (d : ℕ) (hj : Part j) (hr : Res j s t i s' t')
    (hst : ∀ x : T, s x ∈ Set.range j → t x ∈ Set.range j) (hs : FEt s d) : FEt s' d := by
  have := hj.op
  have := hr.op
  have hpre : s ⁻¹ᵁ j.opensRange = i.opensRange := by
    apply SetLike.coe_injective
    change s ⁻¹' Set.range j = Set.range i
    rw [hr.rng]
    ext x
    exact ⟨fun h => ⟨h, hst x h⟩, fun h => h.1⟩
  have pb : IsPullback s' i j s := IsOpenImmersion.isPullback s' i j s hr.es.symm hpre
  obtain ⟨hfin, het, hcard⟩ := hs
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) pb.flip hfin,
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Etale) pb.flip het, ?_⟩
  intro K _ _ x
  rw [← hcard K (x ≫ j)]
  refine Nat.card_congr
    { toFun := fun y => ⟨y.1 ≫ i, by rw [Category.assoc, ← pb.w, ← Category.assoc, y.2]⟩
      invFun := fun z => ⟨pb.lift x z.1 z.2.symm, pb.lift_fst _ _ _⟩
      left_inv := fun y => Subtype.ext (pb.hom_ext (by simp [y.2]) (by simp))
      right_inv := fun z => Subtype.ext (pb.lift_snd _ _ _) }

private theorem fEt_surj {Y X : Scheme.{0}} {f : Y ⟶ X} {d : ℕ} (hf : FEt f d) (hd : 0 < d) (x : X) :
    ∃ y : Y, f y = x := by
  let K := AlgebraicClosure (X.residueField x)
  let b : Spec (CommRingCat.of K) ⟶ Spec (X.residueField x) :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K))
  let a : Spec (CommRingCat.of K) ⟶ X := b ≫ X.fromSpecResidueField x
  have hc := hf.2.2 K a
  obtain ⟨⟨y, hy⟩⟩ := (Nat.card_pos_iff.mp (hc.symm ▸ hd)).1
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  refine ⟨y pt, ?_⟩
  have h1 : a pt ∈ Set.range (X.fromSpecResidueField x) := ⟨b pt, by simp [a]⟩
  rw [X.range_fromSpecResidueField] at h1
  rw [← Scheme.Hom.comp_apply, hy]
  exact h1

private theorem fEt_comp_iso {Y X X' : Scheme.{0}} {f : Y ⟶ X} (e : X ⟶ X') [IsIso e] {d : ℕ}
    (hf : FEt f d) : FEt (f ≫ e) d := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  rw [← h3 K (x ≫ inv e)]
  refine Nat.card_congr ⟨fun y => ⟨y.1, ?_⟩, fun y => ⟨y.1, ?_⟩, fun _ => rfl, fun _ => rfl⟩
  · rw [← cancel_mono e]; simp [y.2]
  · rw [← Category.assoc, y.2]; simp

theorem liesCut (k L O : Type) [Field k] [Field L] [CommRing O] [Algebra O k] (H : HTower k)
    (θ : H.Γ → L) (C C' : Cover H θ O) (j : C'.Y ⟶ C.Y) (hj : Part j) (hπ : C'.π ≫ j = C.π)
    (g : H.Γ) (T : Scheme) (s t : T ⟶ C.Y) (m : ℕ) (hL : C.Lies g s t m) :
    (∀ x : T, s x ∈ Set.range C.π → t x ∈ Set.range C.π) ∧
      ∀ (T' : Scheme) (i : T' ⟶ T) (s' t' : T' ⟶ C'.Y), Res j s t i s' t' → C'.Lies g s' t' m := by
  obtain ⟨hm, κ, h, ht, hF⟩ := hL
  have first : ∀ x : T, s x ∈ Set.range C.π → t x ∈ Set.range C.π := by
    rintro x ⟨z, hz⟩
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback z x hz
    obtain ⟨y, rfl⟩ := fEt_surj hF hm w
    refine ⟨H.t g y, ?_⟩
    have hx : κ y = x := by
      rw [← hw2, ← Scheme.Hom.comp_apply, pullback.lift_snd]
    rw [← hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ht]
  refine ⟨first, ?_⟩
  intro T' i s' t' hR
  have : IsOpenImmersion i := hR.op
  have : IsOpenImmersion j := hj.op
  have hrj : ∀ z, C.π z ∈ Set.range j := fun z =>
    ⟨C'.π z, by rw [← hπ, Scheme.Hom.comp_apply]⟩
  have hκ : Set.range κ ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    rw [hR.rng]
    refine ⟨?_, ?_⟩
    · show s (κ y) ∈ Set.range j
      rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
      exact hrj _
    · show t (κ y) ∈ Set.range j
      rw [← Scheme.Hom.comp_apply, ht, Scheme.Hom.comp_apply]
      exact hrj _
  let κ' : H.Y g ⟶ T' := IsOpenImmersion.lift i κ hκ
  have hκ' : κ' ≫ i = κ := IsOpenImmersion.lift_fac i κ hκ
  have hs' : H.s g ≫ C'.π = κ' ≫ s' := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.es, ← Category.assoc, hκ', h]
  have ht' : κ' ≫ t' = H.t g ≫ C'.π := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.et, ← Category.assoc, hκ', ht]
  refine ⟨hm, κ', hs', ht', ?_⟩
  have hσ : Set.range (pullback.snd C.π s) ⊆ Set.range i := by
    rintro _ ⟨w, rfl⟩
    have hs1 : s (pullback.snd C.π s w) = C.π (pullback.fst C.π s w) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    have hmem : s (pullback.snd C.π s w) ∈ Set.range C.π := ⟨_, hs1.symm⟩
    rw [hR.rng]
    refine ⟨?_, ?_⟩
    · show s (pullback.snd C.π s w) ∈ Set.range j
      rw [hs1]; exact hrj _
    · show t (pullback.snd C.π s w) ∈ Set.range j
      obtain ⟨z, hz⟩ := first _ hmem
      rw [← hz]; exact hrj _
  let σ : pullback C.π s ⟶ T' := IsOpenImmersion.lift i (pullback.snd C.π s) hσ
  have hσ' : σ ≫ i = pullback.snd C.π s := IsOpenImmersion.lift_fac i _ hσ
  have hc : pullback.fst C.π s ≫ C'.π = σ ≫ s' := by
    rw [← cancel_mono j, Category.assoc, Category.assoc, hπ, hR.es, ← Category.assoc, hσ',
      pullback.condition]
  let ψ : pullback C.π s ⟶ pullback C'.π s' := pullback.lift (pullback.fst C.π s) σ hc
  have hc' : pullback.fst C'.π s' ≫ C.π = (pullback.snd C'.π s' ≫ i) ≫ s := by
    rw [← hπ, Category.assoc, ← hR.es, ← Category.assoc, ← Category.assoc, pullback.condition]
  let φ : pullback C'.π s' ⟶ pullback C.π s :=
    pullback.lift (pullback.fst C'.π s') (pullback.snd C'.π s' ≫ i) hc'
  have ψ1 : ψ ≫ pullback.fst C'.π s' = pullback.fst C.π s := pullback.lift_fst _ _ _
  have ψ2 : ψ ≫ pullback.snd C'.π s' = σ := pullback.lift_snd _ _ _
  have φ1 : φ ≫ pullback.fst C.π s = pullback.fst C'.π s' := pullback.lift_fst _ _ _
  have φ2 : φ ≫ pullback.snd C.π s = pullback.snd C'.π s' ≫ i := pullback.lift_snd _ _ _
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, φ1, ψ1, Category.id_comp]
    · rw [Category.assoc, φ2, ← Category.assoc, ψ2, hσ', Category.id_comp]
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, ψ1, φ1, Category.id_comp]
    · rw [Category.assoc, ψ2, Category.id_comp, ← cancel_mono i, Category.assoc, hσ', φ2]
  have : IsIso ψ := ⟨φ, hψφ, hφψ⟩
  have hfac : pullback.lift (H.s g) κ' hs' = pullback.lift (H.s g) κ h ≫ ψ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, ψ1, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, ψ2, ← cancel_mono i, hκ', Category.assoc, hσ',
        pullback.lift_snd]
  rw [hfac]
  exact fEt_comp_iso ψ hF

private theorem multiset_map_pts {J P Q : Type} [Fintype J] {I : J → Type} [∀ j, Fintype (I j)] (a : J → ℕ)
    (v : (j : J) → I j → P) (g : P → Q) :
    Multiset.map g (crystallineComparison.pts a v) = crystallineComparison.pts a (fun j i => g (v j i)) := by
  simp only [crystallineComparison.pts]

  rw [show Multiset.map g = Multiset.mapAddMonoidHom g from rfl, map_sum]
  simp [Multiset.map_nsmul, Multiset.map_map]

private theorem identity_of_comp_injective_semiconj_image (q n : ℕ) {P Q : Type} (F' : P → P) (F : Q → Q) (g : P → Q)
    (hg : Function.Injective g) (hc : Function.Semiconj g F' F) {I : Fin (n + 1) → Type}
    [∀ j, Fintype (I j)] (v : (j : Fin (n + 1)) → I j → P)
    (h : crystallineComparison.AltId q n F (fun j i => g (v j i))) : crystallineComparison.AltId q n F' v := by
  unfold crystallineComparison.AltId at *
  apply Multiset.map_injective hg
  have e : ∀ (k : ℕ) (x : P), F^[k] (g x) = g (F'^[k] x) := fun k x => ((hc.iterate_right k) x).symm
  simp only [e] at h
  rw [multiset_map_pts, multiset_map_pts]
  exact h

private theorem genPt_openImmersion_of_genPt_appTop {Y' Y : Scheme} (j : Y' ⟶ Y) [IsOpenImmersion j] (π : Γ(Y, ⊤)) (x : Y')
    (h : crystallineComparison.GenPt ((ConcreteCategory.hom (Scheme.Hom.appTop j)) π) x) : crystallineComparison.GenPt π (j x) := by
  have key : ∀ y : Y', j y ∈ Y.basicOpen π ↔
      y ∈ Y'.basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop j)) π) := by
    intro y
    rw [← Scheme.preimage_basicOpen_top]
    rfl
  refine ⟨fun hx => h.1 ((key x).1 hx), fun x' hx' hsp => ?_⟩
  obtain ⟨x'', rfl⟩ : x' ∈ Set.range j := hsp.mem_open j.isOpenEmbedding.isOpen_range ⟨x, rfl⟩
  have h2 : x'' ⤳ x := (j.isOpenEmbedding.toIsInducing.specializes_iff).1 hsp
  rw [h.2 x'' (fun hb => hx' ((key x'').2 hb)) h2]

theorem ptIdCut (l q n : ℕ) (Y' Y : Scheme.{0}) (j : Y' ⟶ Y) (π : Γ(Y, ⊤))
    (T : Fin (n + 1) → crystallineComparison.Corr l Y) (T' : Fin (n + 1) → crystallineComparison.Corr l Y')
    (i : ∀ a, (T' a).Z ⟶ (T a).Z) (hP : Part j) (hR : ∀ a, Res j (T a).p (T a).r (i a) (T' a).p (T' a).r)
    (hr : ∀ a (x : (T a).Z), (T a).p x ∈ Set.range j → (T a).p x ∈ Y.basicOpen (l : Γ(Y, ⊤)) → (T a).r x ∈ Set.range j)
    (hT : crystallineComparison.PtId l q n π T) : crystallineComparison.PtId l q n (j.appTop π) T' := by
  unfold crystallineComparison.PtId at hT ⊢
  intro V _ _ _ _ hl y' hg φ hφ I _ z' hz'
  have := hP.op
  let e := fun a => secEquiv hP (hR a) (hr a) hl y'
  let w := fun a => e a ∘ z' a
  have hw := fun a => (e a).bijective.comp (hz' a)
  have hg' : crystallineComparison.GenPt π ((y' ≫ j) (IsLocalRing.closedPoint V)) := by
    have h0 := genPt_openImmersion_of_genPt_appTop j π _ hg
    convert h0 using 1
    exact Scheme.Hom.comp_apply y' j _
  have h := hT V hl (y' ≫ j) hg' φ hφ I w hw
  refine identity_of_comp_injective_semiconj_image q n (crystallineComparison.twist φ Y') (crystallineComparison.twist φ Y) (fun x => x ≫ j)
    (fun x y hxy => (cancel_mono j).1 hxy) (fun x => by simp [crystallineComparison.twist, Category.assoc]) _ ?_
  have he : (fun a b => (crystallineComparison.resPt V ≫ (z' a b).1 ≫ (T' a).r) ≫ j) =
      fun a b => crystallineComparison.resPt V ≫ (w a b).1 ≫ (T a).r := by
    funext a b
    change (crystallineComparison.resPt V ≫ (z' a b).1 ≫ (T' a).r) ≫ j =
      crystallineComparison.resPt V ≫ ((z' a b).1 ≫ i a) ≫ (T a).r
    simp only [Category.assoc, (hR a).et]
  rw [he]
  exact h

theorem resEx (Y' Y T : Scheme.{0}) (j : Y' ⟶ Y) (s t : T ⟶ Y) (hj : Part j) :
    ∃ (T' : Scheme.{0}) (i : T' ⟶ T) (s' t' : T' ⟶ Y'), Res j s t i s' t' := by
  have := hj.op
  let U : T.Opens := s ⁻¹ᵁ j.opensRange ⊓ t ⁻¹ᵁ j.opensRange
  have hs : Set.range (U.ι ≫ s) ⊆ Set.range j := Set.range_subset_iff.mpr fun x => x.2.1
  have ht : Set.range (U.ι ≫ t) ⊆ Set.range j := Set.range_subset_iff.mpr fun x => x.2.2
  refine ⟨U, U.ι, IsOpenImmersion.lift j _ hs, IsOpenImmersion.lift j _ ht,
    ⟨inferInstance, ?_, IsOpenImmersion.lift_fac _ _ _, IsOpenImmersion.lift_fac _ _ _⟩⟩
  rw [Scheme.Opens.range_ι]
  rfl

end UpperTheory.Gal.Int.Geo.Cut
