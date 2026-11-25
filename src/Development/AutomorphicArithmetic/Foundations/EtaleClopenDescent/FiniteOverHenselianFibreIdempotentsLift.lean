module

public import Development.EtaleCohomology.EtaleSheaves.FibreIdem
public import Development.EtaleCohomology.EtaleSheaves.LZProperCut
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.StdChartsProof

namespace UpperTheory.Cb.RestrictionHomomorphisms

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

private abbrev mI (A : Type) [CommRing A] [IsLocalRing A] (S : Type) [CommRing S] [Algebra A S] : Ideal S :=
  (IsLocalRing.maximalIdeal A).map (algebraMap A S)

private lemma mem_mS_iff (S : Subalgebra A K) (s : S) : (s : K) ∈ mS S ↔ s ∈ mI A S := by
  have h1 : Subalgebra.toSubmodule S = Submodule.map S.val.toLinearMap ⊤ := by
    rw [Submodule.map_top]
    ext x
    simp
  show (s : K) ∈ IsLocalRing.maximalIdeal A • Subalgebra.toSubmodule S ↔ _
  rw [h1, ← Submodule.map_smul'', Ideal.smul_top_eq_map]
  constructor
  · rintro ⟨y, hy, hys⟩
    have hy' : y = s := Subtype.ext hys
    subst hy'
    exact hy
  · intro h
    exact ⟨s, h, rfl⟩

private lemma idem_of_clopen {S : Type} [CommRing S] (I : Ideal S) {F : Type} [TopologicalSpace F]
    (g : PrimeSpectrum (S ⧸ I) → F) (hg : Continuous g) (W : Set F) (hW : IsClopen W) :
    ∃ e : S, e * e - e ∈ I ∧ ∀ q : PrimeSpectrum (S ⧸ I),
      g q ∈ W ↔ e ∉ (PrimeSpectrum.comap (Ideal.Quotient.mk I) q).asIdeal := by
  obtain ⟨u, hu, hW'⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen (hW.preimage hg)
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective u
  refine ⟨e, ?_, fun q => ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hu.eq, sub_self]
  · have h := Set.ext_iff.mp hW' q
    rw [Set.mem_preimage] at h
    rw [h, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]

private lemma restr_ex (B : Subalgebra A K) (t : K) (S : Subalgebra A K) (hS : S ≤ AdjoinInv B t)
    (Q : PrimeSpectrum (AdjoinInv B t)) (hQ : mI A (AdjoinInv B t) ≤ Q.asIdeal) :
    ∃ q : PrimeSpectrum (S ⧸ mI A S), Restr B t Q S (PrimeSpectrum.comap (Ideal.Quotient.mk _) q) ∧
      ∀ s : S, s ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk (mI A S)) q).asIdeal ↔
        Subalgebra.inclusion hS s ∈ Q.asIdeal := by
  have hle : mI A S ≤ (PrimeSpectrum.comap (Subalgebra.inclusion hS).toRingHom Q).asIdeal := by
    show Ideal.map _ _ ≤ Ideal.comap _ Q.asIdeal
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, ← Ideal.map_le_iff_le_comap]
    exact hQ
  have ⟨q, hq⟩ : PrimeSpectrum.comap (Subalgebra.inclusion hS).toRingHom Q ∈
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (mI A S))) := by
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      PrimeSpectrum.mem_zeroLocus, Ideal.mk_ker]
    exact SetLike.coe_subset_coe.mpr hle
  refine ⟨q, ?_, fun s => ?_⟩
  · rw [hq]
    intro s
    constructor
    · intro hs
      exact ⟨Subalgebra.inclusion hS s, hs, rfl⟩
    · rintro ⟨d, hd, hds⟩
      have hd' : d = Subalgebra.inclusion hS s := Subtype.ext hds
      rw [hd'] at hd
      exact hd
  · rw [hq]
    rfl

private lemma pair_of_maps (B C : Subalgebra A K) (t : K) (hc : Charts B C t) {F : Type} [TopologicalSpace F]
    (gB : PrimeSpectrum (B ⧸ mI A B) → F) (gC : PrimeSpectrum (C ⧸ mI A C) → F)
    (hgB : Continuous gB) (hgC : Continuous gC)
    (hcov : ∀ w, (∃ q, gB q = w) ∨ ∃ q, gC q = w)
    (hov : ∀ (qB : PrimeSpectrum (B ⧸ mI A B)) (qC : PrimeSpectrum (C ⧸ mI A C)) (Q : PrimeSpectrum (AdjoinInv B t)),
      Restr B t Q B (PrimeSpectrum.comap (Ideal.Quotient.mk _) qB) →
      Restr B t Q C (PrimeSpectrum.comap (Ideal.Quotient.mk _) qC) → gB qB = gC qC)
    (W : Set F) (hW : IsClopen W) :
    ∃ e f : K, IdemPair B C t e f ∧
      ((e ∈ mS B ∧ f ∈ mS C) → W = ∅) ∧ ((e - 1 ∈ mS B ∧ f - 1 ∈ mS C) → W = Set.univ) := by
  obtain ⟨eB, heB, hWB⟩ := idem_of_clopen (mI A B) gB hgB W hW
  obtain ⟨eC, heC, hWC⟩ := idem_of_clopen (mI A C) gC hgC W hW
  have hBD : B ≤ AdjoinInv B t := fun b hb => Algebra.subset_adjoin (Or.inl hb)
  have hCD : C ≤ AdjoinInv B t := by
    rw [hc.glue]
    exact fun c hc' => Algebra.subset_adjoin (Or.inl hc')
  have idem : ∀ (S : Subalgebra A K) (h : S ≤ AdjoinInv B t) (e : S), e * e - e ∈ mI A S →
      IsIdempotentElem (Ideal.Quotient.mk (mI A (AdjoinInv B t)) (Subalgebra.inclusion h e)) := by
    intro S h e he
    have h' := Ideal.mem_map_of_mem (Subalgebra.inclusion h : S →+* AdjoinInv B t) he
    rw [Ideal.map_map, AlgHom.comp_algebraMap, map_sub, map_mul] at h'
    rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.eq]
    exact h'
  have inn : ∀ {S : Subalgebra A K} (e : S) (q : PrimeSpectrum (S ⧸ mI A S)), e ∈ mI A S →
      e ∈ (PrimeSpectrum.comap (Ideal.Quotient.mk (mI A S)) q).asIdeal := fun e q he => by
    simp [Ideal.Quotient.eq_zero_iff_mem.2 he]
  have notin : ∀ {S : Subalgebra A K} (e : S) (q : PrimeSpectrum (S ⧸ mI A S)), e - 1 ∈ mI A S →
      e ∉ (PrimeSpectrum.comap (Ideal.Quotient.mk (mI A S)) q).asIdeal := fun e q he hq =>
    q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem hq (inn (e - 1) q he)))
  set a : AdjoinInv B t := Subalgebra.inclusion hBD eB with ha_def
  set b : AdjoinInv B t := Subalgebra.inclusion hCD eC with hb_def
  have hmem : a - b ∈ mI A (AdjoinInv B t) := by
    refine Ideal.Quotient.eq.1 (PrimeSpectrum.basicOpen_injOn_isIdempotentElem (idem B hBD eB heB) (idem C hCD eC heC) ?_)
    ext Q
    let P := PrimeSpectrum.comap (Ideal.Quotient.mk (mI A (AdjoinInv B t))) Q
    have hPle : mI A (AdjoinInv B t) ≤ P.asIdeal := fun d hd => inn d Q hd
    obtain ⟨qB, hRB, hmB⟩ := restr_ex B t B hBD P hPle
    obtain ⟨qC, hRC, hmC⟩ := restr_ex B t C hCD P hPle
    have h1 := hWB qB
    have h2 := hWC qC
    rw [hov qB qC P hRB hRC, hmB] at h1
    rw [hmC] at h2
    exact h1.symm.trans h2
  refine ⟨(eB : K), (eC : K), ⟨eB.2, eC.2, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (mem_mS_iff B (eB * eB - eB)).2 heB
  · exact (mem_mS_iff C (eC * eC - eC)).2 heC
  · exact (mem_mS_iff (AdjoinInv B t) (a - b)).2 hmem
  · rintro ⟨h1, h2⟩
    have hB' : eB ∈ mI A B := (mem_mS_iff B eB).1 h1
    have hC' : eC ∈ mI A C := (mem_mS_iff C eC).1 h2
    ext w
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    rcases hcov w with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · exact (hWB q).1 hw (inn eB q hB')
    · exact (hWC q).1 hw (inn eC q hC')
  · rintro ⟨h1, h2⟩
    have hB' : eB - 1 ∈ mI A B := (mem_mS_iff B (eB - 1)).1 h1
    have hC' : eC - 1 ∈ mI A C := (mem_mS_iff C (eC - 1)).1 h2
    ext w
    simp only [Set.mem_univ, iff_true]
    rcases hcov w with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · exact (hWB q).2 (notin eB q hB')
    · exact (hWC q).2 (notin eC q hC')

private def resHom (A : Type) [CommRing A] [IsLocalRing A] (S : Type) [CommRing S] [Algebra A S] :
    IsLocalRing.ResidueField A →+* S ⧸ mI A S :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) ((Ideal.Quotient.mk (mI A S)).comp (algebraMap A S))
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha))

private lemma fibre_map {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) {S : Type} [CommRing S] [Algebra A S]
    (j : Spec (CommRingCat.of S) ⟶ Z) (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A S))) :
    ∃ g : Spec (CommRingCat.of (S ⧸ mI A S)) ⟶ pullback p (cpt A),
      g ≫ pullback.fst p (cpt A) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mI A S))) ≫ j := by
  refine ⟨pullback.lift (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mI A S))) ≫ j)
    (Spec.map (CommRingCat.ofHom (resHom A S))) ?_, pullback.lift_fst _ _ _⟩
  rw [Category.assoc, hj, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

private lemma fst_inj {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) :
    Function.Injective (pullback.fst p (cpt A)).base := by
  have h1 : IsClosedImmersion (cpt A) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  have h2 : IsClosedImmersion (pullback.fst p (cpt A)) := inferInstance
  exact (pullback.fst p (cpt A)).isClosedEmbedding.injective

private lemma g_apply {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) {S : Type} [CommRing S] [Algebra A S]
    (j : Spec (CommRingCat.of S) ⟶ Z) (g : Spec (CommRingCat.of (S ⧸ mI A S)) ⟶ pullback p (cpt A))
    (hg : g ≫ pullback.fst p (cpt A) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mI A S))) ≫ j)
    (q : PrimeSpectrum (S ⧸ mI A S)) :
    (pullback.fst p (cpt A)).base (g.base q) =
      j.base (PrimeSpectrum.comap (Ideal.Quotient.mk (mI A S)) q) := by
  exact congrArg (fun h => h.base q) hg

private lemma fibre_pt {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) {S : Type} [CommRing S] [Algebra A S]
    (j : Spec (CommRingCat.of S) ⟶ Z) (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A S)))
    (g : Spec (CommRingCat.of (S ⧸ mI A S)) ⟶ pullback p (cpt A))
    (hg : g ≫ pullback.fst p (cpt A) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (mI A S))) ≫ j)
    (w : ↑(pullback p (cpt A))) (x : PrimeSpectrum S)
    (hx : j.base x = (pullback.fst p (cpt A)).base w) : ∃ q, g.base q = w := by
  have h1 : p.base (j.base x) = (cpt A).base ((pullback.snd p (cpt A)).base w) := by
    rw [hx]
    exact congrArg (fun (h : pullback p (cpt A) ⟶ Spec (CommRingCat.of A)) => h.base w)
      (pullback.condition (f := p) (g := cpt A))
  have h2 : p.base (j.base x) = PrimeSpectrum.comap (algebraMap A S) x :=
    congrArg (fun h => h.base x) hj
  have hm : mI A S ≤ x.asIdeal := by
    have h3 : (PrimeSpectrum.comap (algebraMap A S) x).asIdeal = IsLocalRing.maximalIdeal A := by
      rw [← h2, h1]
      let y : PrimeSpectrum (IsLocalRing.ResidueField A) := (pullback.snd p (cpt A)).base w
      have hbot : y.asIdeal = ⊥ := by
        haveI := y.isPrime
        exact Ideal.eq_bot_of_prime y.asIdeal
      show Ideal.comap (IsLocalRing.residue A) y.asIdeal = _
      rw [hbot, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
    show Ideal.map _ _ ≤ _
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq h3.symm
  have ⟨q, hq⟩ : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (mI A S))) := by
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      PrimeSpectrum.mem_zeroLocus, Ideal.mk_ker]
    exact SetLike.coe_subset_coe.mpr hm
  refine ⟨q, fst_inj p ?_⟩
  rw [g_apply p j g hg q, hq, hx]

end UpperTheory.Cb.RestrictionHomomorphisms

open UpperTheory.Cb.RestrictionHomomorphisms in
theorem UpperTheory.Cb.finite_over_henselian_fibre_idempotents_lift :
    LateralTheory.E.LZProperCut.LZHensFinite → LateralTheory.E.StdChartsProof.FibreIdem := by
  intro _ A _ _ K _ _ Z p B C t hc hcov W hW
  obtain ⟨jU, jV, _, _, hrange, hU, hV, hiff⟩ := hcov.ex
  obtain ⟨gB, hgB⟩ := fibre_map p jU hU
  obtain ⟨gC, hgC⟩ := fibre_map p jV hV
  refine pair_of_maps B C t hc (fun q => gB.base q) (fun q => gC.base q)
    gB.base.hom.continuous gC.base.hom.continuous ?_ ?_ W hW
  · intro w
    have hw : (pullback.fst p (cpt A)).base w ∈ Set.range jU ∪ Set.range jV := by
      rw [hrange]
      exact Set.mem_univ _
    rcases hw with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact Or.inl (fibre_pt p jU hU gB hgB w x hx)
    · exact Or.inr (fibre_pt p jV hV gC hgC w y hy)
  · intro qB qC Q hB hC
    apply fst_inj p
    rw [g_apply p jU gB hgB qB, g_apply p jV gC hgC qC]
    exact (hiff _ _).2 ⟨Q, hB, hC⟩
