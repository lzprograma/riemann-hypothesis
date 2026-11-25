module

import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderBound
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.BlowupDataOfSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackCriterion
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Prepend

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReductionEmptyOrderLocus

private theorem blowupMorphism_mem_orderAtLeastLocus {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E) (hm : 1 ≤ m)
    (hsm : ∀ i, i ≤ s.length → AlgebraicGeometry.Smooth (MarkedSequenceOfBlowups.projectionToSpec s i))
    (hno : ∀ i, i ≤ s.length → AlgebraicGeometry.IsNoetherian (s.schemeAt i))
    (i : ℕ) (hi : i < s.length) (z : s.schemeAt (i + 1))
    (hz : z ∈ orderAtLeastLocus (s.ideal (i + 1)) m) :
    (s.transitionMapSucc i) z ∈ orderAtLeastLocus (s.ideal i) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  have := hsm i hi.le
  have := hno (i + 1) hi
  have hsnc : HasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec s i) (s.center i) (s.boundary i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_snc i hi
  have hord : (↑(s.center i).support : Set (s.schemeAt i)) ⊆ orderAtLeastLocus (s.ideal i) n :=
    (s.center_order i hi).trans
      (orderAtLeastLocus_subset_of_le (s.ideal i) (Nat.le_succ n))
  have hI : s.ideal i ≤ s.center i ^ n :=
    le_pow_of_hasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec s i) (s.center i) (s.ideal i)
      (s.boundary i) hsnc n hord
  have hpb : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) (s.center i) := s.isBlowupAlongIdealSheaf_blowupMorphism i hi
  have key := orderAtLeastLocus_controlledTransform_subset_preimage k
      (MarkedSequenceOfBlowups.projectionToSpec s i) (s.transitionMapSucc i) (s.center i) (s.boundary i) hsnc hpb
      (s.ideal i) n hI
  have hmul : Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) ^ n *
      (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) * s.ideal (i + 1))
      = (s.ideal i).comap (s.transitionMapSucc i) := by
    rw [← mul_assoc, ← pow_succ]
    exact s.ideal_succ i hi
  have heq := eq_controlledTransform_of_mul_eq_comap (s.transitionMapSucc i) (s.center i) (s.ideal i) n hpb hI
      (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) * s.ideal (i + 1)) hmul
  have hz' : z ∈ orderAtLeastLocus
      (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) * s.ideal (i + 1)) (n + 1) := by
    rw [mem_orderAtLeastLocus_iff] at hz ⊢
    exact hz.trans ((self_le_add_left _ _).trans
      (add_orderAt_le_orderAt_mul (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i))
        (s.ideal (i + 1)) z))
  rw [heq] at hz'
  exact key hz'

private theorem projectionToBase_mem_orderAtLeastLocus {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) (s : T.SequenceOfBlowups) :
    ∀ i, i ≤ s.length → ∀ z : s.schemeAt i,
      z ∈ orderAtLeastLocus (s.ideal i) T.mult → (s.projectionToBase i) z ∈ orderAtLeastLocus T.ideal T.mult := by
  have := hV.charZero
  intro i
  induction i with
  | zero =>
      intro _ z hz
      rw [markedSequenceOfBlowups_ideal_zero s, MarkedSequenceOfBlowups.projectionToBase_zero s, orderAtLeastLocus_comap_iso_hom_eq_preimage] at hz
      rw [MarkedSequenceOfBlowups.projectionToBase_zero s]
      exact hz
  | succ i ih =>
      intro hi z hz
      rw [MarkedSequenceOfBlowups.projectionToBase_succ_apply]
      refine ih (Nat.le_of_succ_le hi) _ ?_
      exact blowupMorphism_mem_orderAtLeastLocus s hV.one_le_mult
        (fun j hj => MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s j hj)
        (fun j hj => MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s j hj)
        i (Nat.lt_of_succ_le hi) z hz

theorem center_disjoint_range_of_preimage_orderAtLeastLocus_eq_empty
    {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) {Y : Scheme.{u}} (h : Y ⟶ T.scheme)
    (hempty : (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) = ∅) (s : T.SequenceOfBlowups) :
    ∀ i < s.length, ∀ z : s.schemeAt i, z ∈ (s.center i).support →
      ∀ y : Y, h y ≠ (s.projectionToBase i) z := by
  intro i hi z hz y hy
  have hz' : z ∈ (↑((s.center i).support) : Set (s.schemeAt i)) := hz
  have hzc : z ∈ orderAtLeastLocus (s.ideal i) T.mult := s.center_order i hi hz'
  have himg := projectionToBase_mem_orderAtLeastLocus hV s i hi.le z hzc
  rw [← hy] at himg
  have hmem : y ∈ (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) := himg
  rw [hempty] at hmem
  simp at hmem

theorem isPullbackSequenceOfBlowups_of_preimage_orderAtLeastLocus_empty
    {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) {Y : Scheme.{u}} (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Flat h]
    (hempty : (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) = ∅) (s : T.SequenceOfBlowups)
    (B' : SequenceOfBlowups Y) (hB' : B'.length = 0) :
    IsPullbackBlowupSequence h B' s.toSequenceOfBlowups := by
  have hdisj := center_disjoint_range_of_preimage_orderAtLeastLocus_eq_empty hV h hempty s
  refine (SequenceOfBlowupsPullback.ofBlowupDataOfSeq
      (SequenceOfBlowupsPullback.ofCentersMissImage h (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups)
        (by
          intro i hi z hz y
          rw [BlowupSequenceData.ofSequenceOfBlowups_projectionToBase]
          exact hdisj i hi z hz y)
        (BlowupSequenceData.ofSequenceOfBlowups B') (by exact hB'))).isPullbackSequenceOfBlowups

end DivisorReductionEmptyOrderLocus

theorem BlowupSequenceData.prepend_toSequenceOfBlowups_congr {X : Scheme.{u}} {Z Z' : X.IdealSheafData} (hZZ : Z = Z')
    (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (hZ' : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z') (d : BlowupSequenceData X) :
    (BlowupSequenceData.prepend Z hZ d).toSequenceOfBlowups = (BlowupSequenceData.prepend Z' hZ' d).toSequenceOfBlowups := by
  subst hZZ
  rfl

namespace DivisorReduction

private theorem markedIdealWithBoundary_mk_ideal_congr {k : Type u} [inst : Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ} {E : List X.IdealSheafData}
    {I₁ I₂ : X.IdealSheafData} (hI : I₁ = I₂) :
    (@MarkedIdealWithBoundary.mk k inst X p I₁ m E) = (@MarkedIdealWithBoundary.mk k inst X p I₂ m E) := by
  rw [hI]

private theorem isPullbackSequenceOfBlowups_apply_congr (L : PrincipalizationAssignment.{u})
    {X : Scheme.{u}} (B : SequenceOfBlowups X) (S S' : MarkedIdealWithBoundary.{u}) (hS : S = S')
    (φ : S.scheme ⟶ X) (φ' : S'.scheme ⟶ X) (hφ : HEq φ φ')
    (hpb : IsPullbackBlowupSequence φ (L S).toSequenceOfBlowups B) :
    IsPullbackBlowupSequence φ' (L S').toSequenceOfBlowups B := by
  subst hS
  have hee : φ = φ' := eq_of_heq hφ
  subst hee
  exact hpb

private theorem pullback_restriction {n : ℕ} {L O : PrincipalizationAssignment.{u}}
    (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [Smooth h]
    (hq : h ≫ T.structMap = q) (E : List Y.IdealSheafData) (k : ℕ) (hk : k < E.length)
    (hD : E.get ⟨k, hk⟩ = (T.boundary.get ⟨j, hj⟩).comap h)
    (I : T.scheme.IdealSheafData) (F : List T.scheme.IdealSheafData)
    (I' : Y.IdealSheafData) (F' : List Y.IdealSheafData)
    (hI : I' = I.comap h)
    (hF : MarkedIdealWithBoundary.SameNontrivialBoundary ((F'.eraseIdx k).take (E.length - 1))
      (((F.eraseIdx j).take (T.boundary.length - 1)).map fun D => D.comap h))
    (hV : (restrictToBoundaryDivisor T j hj I F).IsAdmissible)
    (hd : (restrictToBoundaryDivisor T j hj I F).krullDimSucc < n)
    (hV' : (restrictToBoundaryDivisor ((T.pullbackAlong Y q h).withBoundary E) k hk I' F').IsAdmissible)
    (hd' : (restrictToBoundaryDivisor ((T.pullbackAlong Y q h).withBoundary E) k hk I' F').krullDimSucc < n) :
    IsPullbackBlowupSequence (subschemeMapOfComap h _ _ hD)
      (L (restrictToBoundaryDivisor ((T.pullbackAlong Y q h).withBoundary E) k hk I' F')).toSequenceOfBlowups
      (L (restrictToBoundaryDivisor T j hj I F)).toSequenceOfBlowups := by
  let S := restrictToBoundaryDivisor T j hj I F
  let S' := restrictToBoundaryDivisor ((T.pullbackAlong Y q h).withBoundary E) k hk I' F'
  let g := subschemeMapOfComap h _ _ hD
  have hg : Smooth g := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Smooth) (isPullback_subschemeMapOfComap _ _ h _ _ hD).flip inferInstance
  have hq' : g ≫ S.structMap = S'.structMap := by
    change g ≫ _ ≫ T.structMap = (E.get ⟨k, hk⟩).subschemeι ≫ q
    rw [← Category.assoc, subschemeMapOfComap_comp, Category.assoc, hq]
  have hEq : (S.pullbackAlong S'.scheme S'.structMap g).withBoundary S'.boundary = S' := by
    apply markedIdealWithBoundary_mk_ideal_congr
    rw [hI]
    exact comap_subschemeMapOfComap h _ _ hD I
  have hF' : MarkedIdealWithBoundary.SameNontrivialBoundary (S.pullbackAlong S'.scheme S'.structMap g).boundary S'.boundary :=
    (sameNontrivialBoundary_comap_subschemeι h _ _ hD _ _ hF).symm
  have hg' : Smooth (show S'.scheme ⟶ S.scheme from g) := hg
  have hpb := hL.smooth_pullback S hV hd S'.scheme S'.structMap g hq' S'.boundary hF'
    (hEq.symm ▸ hV') (hEq.symm ▸ hd')
  exact isPullbackSequenceOfBlowups_apply_congr L _ _ _ hEq _ _ (HEq.refl g) hpb

/-- Compare divisor reduction along a smooth map carrying the chosen divisor to its pullback.
The chosen entries may have different indices. After erasing them, the boundaries need only
agree up to unit ideals. -/
private theorem divisorFamily_pullback {hres : Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (facts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    {n : ℕ} {L O : PrincipalizationAssignment.{u}} (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (hd : T.krullDimSucc ≤ n)
    (ho : T.IsOrderBoundedByMult) (hb : T.IsBalanced hT.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [Smooth h]
    (hq : h ≫ T.structMap = q) (E : List Y.IdealSheafData) (k : ℕ) (hk : k < E.length)
    (hD : E.get ⟨k, hk⟩ = (T.boundary.get ⟨j, hj⟩).comap h)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary
      (E.eraseIdx k) ((T.boundary.eraseIdx j).map fun D => D.comap h))
    (hV : ((T.pullbackAlong Y q h).withBoundary E).IsAdmissible)
    (hd' : ((T.pullbackAlong Y q h).withBoundary E).krullDimSucc ≤ n)
    (ho' : ((T.pullbackAlong Y q h).withBoundary E).IsOrderBoundedByMult)
    (hb' : ((T.pullbackAlong Y q h).withBoundary E).IsBalanced hV.locallyOfFiniteType)
    (hZ : containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E) k hk =
      (containedComponentsIdeal T j hj).comap h) :
    IsPullbackBlowupSequence h
      (((canonicalAlgorithmRules hres).divisorFamily L k ((T.pullbackAlong Y q h).withBoundary E)).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) := by
  classical
  let S := (T.pullbackAlong Y q h).withBoundary E
  have hNY : IsNoetherian Y := hV.isNoetherian
  have hNS : IsNoetherian S.scheme := hV.isNoetherian
  have hNX := hT.isNoetherian
  have hchr := hT.charZero
  have hsm := hT.smooth
  have hcos : orderAtLeastLocus S.ideal S.mult = h ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    orderAtLeastLocus_comap T.base T.structMap h T.ideal T.mult
  by_cases hn' : (orderAtLeastLocus S.ideal S.mult).Nonempty
  swap
  · have he := Set.not_nonempty_iff_eq_empty.mp hn'
    exact DivisorReductionEmptyOrderLocus.isPullbackSequenceOfBlowups_of_preimage_orderAtLeastLocus_empty hT h
      (hcos.symm.trans he) _ _
      (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L k S hV hd' ho' hb' hk he)
  have hn : (orderAtLeastLocus T.ideal T.mult).Nonempty := by
    rw [hcos] at hn'
    exact hn'.image h |>.mono (Set.image_preimage_subset ..)
  have hg := isPullback_subschemeMapOfComap _ _ h _ _ hD
  have hI := lowerIdeal_comap T hT j hj q h E k hk hV hZ
  have hF := lowerBoundary_comap T hT j hj q h E k hk hV hZ hE
  change MarkedIdealWithBoundary.SameNontrivialBoundary
    (((lowerBoundaryAfterBlowup S k hk).eraseIdx k).take (S.boundary.length - 1)) _ at hF
  have hamb (I F I' F') (hl : I' = I.comap h)
      (hB : MarkedIdealWithBoundary.SameNontrivialBoundary ((F'.eraseIdx k).take (E.length - 1))
        (((F.eraseIdx j).take (T.boundary.length - 1)).map fun D => D.comap h))
      (hv₁ : (restrictToBoundaryDivisor T j hj I F).IsAdmissible)
      (hv₂ : (restrictToBoundaryDivisor S k hk I' F').IsAdmissible) (hpr hpr') :
      IsPullbackBlowupSequence h (ambientBlowupSeq hres blowupPreservesNoetherian S k hk I' F' (L _) hpr').toSequenceOfBlowups
        (ambientBlowupSeq hres blowupPreservesNoetherian T j hj I F (L _) hpr).toSequenceOfBlowups := by
    have hs := pullback_restriction hL T j hj q h hq E k hk hD I F I' F' hl hB hv₁
      ((facts.lowerTriple_dim_lt T hT hn j hj I F).trans_le hd) hv₂
      ((facts.lowerTriple_dim_lt S hV hn' k hk I' F').trans_le hd')
    obtain ⟨comparison⟩ := hs.nonempty_sequenceOfBlowupsPullback
    exact facts.isPullbackSeq_ambientTower _ _ _ _ _ _ _ _ hg.flip _ _ hpr hpr'
      comparison.toBlowupDataOfSeq.isPullbackSequenceOfBlowups
  change IsPullbackBlowupSequence h (((canonicalAlgorithmRules hres).divisorFamily L k S).toSequenceOfBlowups) _
  rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L j,
    divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq hres L k]
  rcases divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres facts L j T hT hj ho hb hn.ne_empty with
    ⟨h₁, pr, mk, e⟩ | ⟨h₁, bl, pr, mk, e⟩ <;>
    rcases divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres facts L k S hV hk ho' hb' hn'.ne_empty with
      ⟨h₂, pr', mk', e'⟩ | ⟨h₂, bl', pr', mk', e'⟩
  · rw [e mk, e' mk', BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
      BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
    rw [lowerIdeal_eq_of_top T j hj h₁, lowerIdeal_eq_of_top S k hk h₂] at hI
    rw [lowerBoundary_erase_of_top T hT j hj h₁, lowerBoundary_erase_of_top S hV k hk h₂] at hF
    exact hamb _ _ _ _ hI hF (facts.valid_lowerTop T hT ho hb j hj h₁) (facts.valid_lowerTop S hV ho' hb' k hk h₂) pr pr'
  · have htop := congrArg (fun Z : T.scheme.IdealSheafData => Z.comap h) h₁
    exact (h₂ (hZ.trans (htop.trans (Scheme.IdealSheafData.comap_top h)))).elim
  · rw [e mk, e' mk', BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
      BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
    refine IsPullbackBlowupSequence.prepend_of_comap_eq_top ?_ _ bl (hZ.symm.trans h₂)
    rw [lowerIdeal_eq_of_top S k hk h₂] at hI
    rw [lowerBoundary_erase_of_top S hV k hk h₂] at hF
    exact hamb _ _ _ _ hI hF (facts.valid_lowerPre T hT ho hb j hj h₁) (facts.valid_lowerTop S hV ho' hb' k hk h₂) pr pr'
  · have hbl : Blowup.IsBlowupAlongIdealSheaf (𝟙 Y) ((containedComponentsIdeal T j hj).comap h) := hZ ▸ bl'
    rw [e mk, e' mk', BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
      BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
      BlowupSequenceData.prepend_toSequenceOfBlowups_congr hZ bl' hbl]
    refine IsPullbackBlowupSequence.prepend_of_comap_ne_top ?_ _ bl hbl (fun ht => h₂ (hZ.trans ht))
    exact hamb _ _ _ _ hI hF (facts.valid_lowerPre T hT ho hb j hj h₁) (facts.valid_lowerPre S hV ho' hb' k hk h₂) pr pr'

private theorem get_append_cons_length {X : Scheme.{u}} (E₁ : List X.IdealSheafData)
    (D : X.IdealSheafData) (E₂ : List X.IdealSheafData)
    (h : E₁.length < (E₁ ++ D :: E₂).length) :
    (E₁ ++ D :: E₂).get ⟨E₁.length, h⟩ = D := by
  induction E₁ with
  | nil => rfl
  | cons a l ih => exact ih _

private theorem eraseIdx_append_cons_length {X : Scheme.{u}} (E₁ : List X.IdealSheafData)
    (D : X.IdealSheafData) (E₂ : List X.IdealSheafData) :
    (E₁ ++ D :: E₂).eraseIdx E₁.length = E₁ ++ E₂ := by
  induction E₁ with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem isomorphic_of_isStrictPullbackAlongId {X : Scheme.{u}} (A B : SequenceOfBlowups X)
    (h : IsStrictPullbackBlowupSeq (𝟙 X) A B) : A.Isomorphic B := by
  unfold IsStrictPullbackBlowupSeq at h
  obtain ⟨hlen, σ, h0, hpb, hc⟩ := h
  have hiso : ∀ (i : ℕ) (hi : i ≤ A.length), IsIso (σ i hi) := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hh : σ 0 hi = A.isoZero.hom ≫ B.isoZero.inv := by
          rw [Iso.eq_comp_inv]
          simpa using h0
        rw [hh]
        infer_instance
    | succ k ih =>
        intro hi
        have hk : k < A.length := hi
        exact (hpb k hk).isIso_fst_of_isIso (ih (le_of_lt hk))
  unfold SequenceOfBlowups.Isomorphic
  exact ⟨hlen, fun i hi => @asIso Scheme _ _ _ (σ i hi) (hiso i hi), by simpa using h0,
    fun i hi => (hpb i hi).w, fun i hi => (hc i hi).symm⟩

theorem isBoundaryPositionInvariant_divisorFamily {hres : Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (facts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    {n : ℕ} {L O : PrincipalizationAssignment.{u}} (hL : IsMaxOrderReduction (fun d => d < n) L O) :
    IsBoundaryPositionInvariant (fun d => d ≤ n) ((canonicalAlgorithmRules hres).divisorFamily L) := by
  constructor
  intro T hd ho hft hb A B A' B' D hA hB hV hV'
  let S := T.withBoundary (A' ++ D :: B')
  let E := A ++ D :: B
  have hj : A'.length < S.boundary.length := by
    change A'.length < (A' ++ D :: B').length
    simp
  have hk : A.length < E.length := by simp [E]
  have hD : E.get ⟨A.length, hk⟩ = (S.boundary.get ⟨A'.length, hj⟩).comap (𝟙 T.scheme) := by
    change (A ++ D :: B).get _ = ((A' ++ D :: B').get _).comap _
    exact (get_append_cons_length A D B hk).trans
      ((get_append_cons_length A' D B' hj).symm.trans (Scheme.IdealSheafData.comap_id _).symm)
  have hE : MarkedIdealWithBoundary.SameNontrivialBoundary (E.eraseIdx A.length)
      ((S.boundary.eraseIdx A'.length).map fun J => J.comap (𝟙 T.scheme)) := by
    change MarkedIdealWithBoundary.SameNontrivialBoundary ((A ++ D :: B).eraseIdx _)
      (((A' ++ D :: B').eraseIdx _).map _)
    rw [eraseIdx_append_cons_length, eraseIdx_append_cons_length]
    exact (hA.append hB).trans (by
      change MarkedIdealWithBoundary.SameNontrivialBoundary (A' ++ B') ((A' ++ B').map fun J : T.scheme.IdealSheafData => J.comap (𝟙 T.scheme))
      simp only [Scheme.IdealSheafData.comap_id, List.map_id_fun', id_eq]
      exact MarkedIdealWithBoundary.SameNontrivialBoundary.refl _)
  let U := (S.pullbackAlong T.scheme T.structMap (𝟙 T.scheme)).withBoundary E
  have hu : U = T.withBoundary E := by
    apply markedIdealWithBoundary_mk_ideal_congr
    exact Scheme.IdealSheafData.comap_id _
  have hvU : U.IsAdmissible := hu.symm ▸ hV
  have hoU : U.IsOrderBoundedByMult := hu.symm ▸ ho
  have hbU : U.IsBalanced hvU.locallyOfFiniteType := by
    change IsDerivBalanced T.base T.structMap (T.ideal.comap (𝟙 T.scheme)) T.mult
    rwa [Scheme.IdealSheafData.comap_id]
  have hZ : containedComponentsIdeal U A.length hk =
      (containedComponentsIdeal S A'.length hj).comap (𝟙 T.scheme) := by
    have hget : E.get ⟨A.length, hk⟩ = S.boundary.get ⟨A'.length, hj⟩ := hD.trans (Scheme.IdealSheafData.comap_id _)
    exact (containedComponentsIdeal_congr T _ _ E S.boundary _ _ hk hj
      (Scheme.IdealSheafData.comap_id _) hget).trans (Scheme.IdealSheafData.comap_id _).symm
  have hs := @divisorFamily_pullback hres facts n L O hL S hV' hd ho hb A'.length hj T.scheme T.structMap (𝟙 T.scheme)
    (inferInstanceAs (Smooth (𝟙 T.scheme))) (Category.id_comp _) E A.length hk hD hE hvU hd hoU hbU hZ
  have hs' := isPullbackSequenceOfBlowups_apply_congr ((canonicalAlgorithmRules hres).divisorFamily L A.length)
    _ U (T.withBoundary E) hu (𝟙 T.scheme) (𝟙 T.scheme) HEq.rfl hs
  apply isomorphic_of_isStrictPullbackAlongId
  exact @IsPullbackBlowupSequence.isStrictPullback_of_surjective _ _ (𝟙 T.scheme)
    (inferInstanceAs (AlgebraicGeometry.Surjective (𝟙 T.scheme))) _ _ hs' fun i hi =>
    (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp
      (divisorFamily_canonicalAlgorithmRules_center_nonempty hres facts n L O hL A'.length S hV' hd ho hb hj i hi)

theorem divisorFamily_pullback_of_smooth {hres : Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (facts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    {n : ℕ} {L O : PrincipalizationAssignment.{u}} (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (hd : T.krullDimSucc ≤ n)
    (ho : T.IsOrderBoundedByMult) (hb : T.IsBalanced hT.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length)
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [Smooth h]
    (hq : h ≫ T.structMap = q) (E : List Y.IdealSheafData)
    (hE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E)
    (htake : E.take (j + 1) = (T.pullbackAlong Y q h).boundary.take (j + 1))
    (hV : ((T.pullbackAlong Y q h).withBoundary E).IsAdmissible)
    (hd' : ((T.pullbackAlong Y q h).withBoundary E).krullDimSucc ≤ n)
    (ho' : ((T.pullbackAlong Y q h).withBoundary E).IsOrderBoundedByMult)
    (hb' : ((T.pullbackAlong Y q h).withBoundary E).IsBalanced hV.locallyOfFiniteType)
    (hk : j < E.length) :
    IsPullbackBlowupSequence h
      (((canonicalAlgorithmRules hres).divisorFamily L j ((T.pullbackAlong Y q h).withBoundary E)).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups) := by
  let S := T.pullbackAlong Y q h
  have hj' : j < S.boundary.length := by simpa [S, MarkedIdealWithBoundary.pullbackAlong] using hj
  have hget := get_eq_get_of_take_succ_eq E S.boundary j htake hk hj'
  refine divisorFamily_pullback facts hL T hT hd ho hb j hj q h hq E j hk
    (hget.trans (by simp [S, MarkedIdealWithBoundary.pullbackAlong])) ?_ hV hd' ho' hb' ?_
  · rw [← List.eraseIdx_map]
    exact hE.symm.eraseIdx j htake
  · refine (containedComponentsIdeal_congr S S.ideal S.ideal E S.boundary j j hk hj' rfl hget).trans ?_
    apply facts.preIdeal_pullbackAlong T hT Y q h hq _ j hj hj'
    exact isAdmissible_of_withBoundary_isAdmissible _ E hE hV

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
