module

public import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafRankPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafShrinkPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafSpanPf
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Tactic.Linter.Style

section
@[expose] public section

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafSecPf

theorem LeafSec_of : LateralTheory.CohomologicalPurity.ChartCut.LeafSec := by
  intro A T _ _ φ I μ hφ hμ
  algebraize [φ]
  have : Algebra.Etale A T := RingHom.etale_algebraMap.mp hφ
  set J : Ideal T := I.map φ with hJ
  have hle : I ≤ J.comap φ := Ideal.le_comap_map
  have hker : ∀ a ∈ J, μ a = 0 := by
    intro a ha
    have : J ≤ RingHom.ker μ := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro c hc
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      rw [← RingHom.comp_apply, hμ]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hc
    exact this ha
  let q : A ⧸ I →+* T ⧸ J := Ideal.quotientMap J φ hle
  let μb : T ⧸ J →+* A ⧸ I := Ideal.Quotient.lift J μ hker
  have hμq : ∀ z, μb (q z) = z := by
    intro z
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    show μb (Ideal.Quotient.mk J (φ c)) = _
    simp only [μb, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply, hμ]
  let g : T →ₐ[A] T ⧸ J :=
    { (q.comp μ) with
      commutes' := fun a => by
        show q (μ (φ a)) = Ideal.Quotient.mk J (φ a)
        rw [← RingHom.comp_apply μ φ, hμ]; rfl }
  let f : T →ₐ[A] T ⧸ J := Ideal.Quotient.mkₐ A J
  let ψ : T ⊗[A] T →ₐ[A] T ⧸ J := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have key : ∀ x : T ⊗[A] T, μb (ψ x) = μ (Algebra.TensorProduct.lmul' A x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [ψ, Algebra.TensorProduct.lift_tmul, map_mul, Algebra.TensorProduct.lmul'_apply_tmul]
      congr 1
      all_goals first | rfl | exact hμq _
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (ψ (Algebra.FormallyUnramified.elem A T))
  refine ⟨t, ?_, ?_⟩
  · have h1 : μb (Ideal.Quotient.mk J t) = μ t := Ideal.Quotient.lift_mk _ _ _
    rw [← h1, ht, key, Algebra.FormallyUnramified.lmul_elem, map_one]
  · intro s hs
    have h2 := congrArg ψ (Algebra.FormallyUnramified.one_tmul_mul_elem (R := A) s)
    simp only [map_mul, ψ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at h2
    have hg : g s = 0 := by show q (μ s) = 0; rw [hs, map_zero]
    rw [hg, zero_mul] at h2
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, ht, mul_comm]
    exact h2.symm

end LateralTheory.CohomologicalPurity.LeafSecPf
end
end
end


section
@[expose] public section

noncomputable section
open MvPolynomial TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafPolyPf

theorem one_tmul_algebraMap {P S A : Type} [CommRing P] [CommRing S] [CommRing A] [Algebra P S] [Algebra P A]
    (p : P) : (1 : S) ⊗ₜ[P] algebraMap P A p = algebraMap P S p ⊗ₜ[P] (1 : A) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

def kap (d e : ℕ) (R : Type) [CommRing R] :
    MvPolynomial (Fin d ⊕ Fin e) R →+* MvPolynomial (Fin d) (MvPolynomial (Fin e) R) :=
  eval₂Hom (C.comp C) (Sum.elim 0 fun i => C (X i))

theorem leafPoly : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := by
  intro e d R A _ _ φ I x y h
  obtain ⟨hψ, hI⟩ := h
  set ψ := MvPolynomial.eval₂Hom φ (Sum.elim x y) with hψdef
  let P := MvPolynomial (Fin d ⊕ Fin e) R
  let S := MvPolynomial (Fin d) (MvPolynomial (Fin e) R)
  let Cc := MvPolynomial (Fin d) (A ⧸ I)
  letI : Algebra P A := ψ.toAlgebra
  letI : Algebra P S := (kap d e R).toAlgebra
  letI : Algebra S (S ⊗[P] A) := Algebra.TensorProduct.leftAlgebra (R := P) (A := S) (B := A)
  have hb : (algebraMap S (S ⊗[P] A)).Etale :=
    RingHom.IsStableUnderBaseChange.tensorProduct RingHom.Etale.isStableUnderBaseChange S hψ
  have hx : ∀ j, x j ∈ I := fun j => hI ▸ Ideal.subset_span ⟨j, rfl⟩
  have hψX : ∀ i, ψ (X i) = Sum.elim x y i := fun i => by simp [ψ]
  let gy : MvPolynomial (Fin e) R →+* A ⧸ I := eval₂Hom ((Ideal.Quotient.mk I).comp φ) fun i => Ideal.Quotient.mk I (y i)
  let FS : S →+* Cc := eval₂Hom ((C : A ⧸ I →+* Cc).comp gy) X
  let ρ : P →+* Cc := (C : A ⧸ I →+* Cc).comp ((Ideal.Quotient.mk I).comp ψ)
  letI : Algebra P Cc := ρ.toAlgebra
  have hFSC : ∀ p, FS (C p) = C (gy p) := fun p => MvPolynomial.eval₂Hom_C _ _ _
  have hFSX : ∀ j, FS (X j) = X j := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have hgC : ∀ r, gy (C r) = Ideal.Quotient.mk I (φ r) := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have hgX : ∀ i, gy (X i) = Ideal.Quotient.mk I (y i) := fun i => MvPolynomial.eval₂Hom_X' _ _ _
  have kC : ∀ r, kap d e R (C r) = C (C r) := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have kl : ∀ j, kap d e R (X (Sum.inl j)) = 0 := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have kr : ∀ i, kap d e R (X (Sum.inr i)) = C (X i) := fun i => MvPolynomial.eval₂Hom_X' _ _ _
  have ψC : ∀ r, ψ (C r) = φ r := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have hFS : FS.comp (kap d e R) = ρ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show FS (kap d e R (C r)) = C (Ideal.Quotient.mk I (ψ (C r)))
      rw [kC, hFSC, hgC, ψC]
    · rintro (j | i)
      · show FS (kap d e R (X (Sum.inl j))) = C (Ideal.Quotient.mk I (ψ (X (Sum.inl j))))
        rw [kl, hψX, map_zero]; simp [Ideal.Quotient.eq_zero_iff_mem.mpr (hx j)]
      · show FS (kap d e R (X (Sum.inr i))) = C (Ideal.Quotient.mk I (ψ (X (Sum.inr i))))
        rw [kr, hFSC, hgX, hψX]; rfl
  let fS : S →ₐ[P] Cc := { FS with commutes' := fun p => RingHom.congr_fun hFS p }
  let fA : A →ₐ[P] Cc := { (C : A ⧸ I →+* Cc).comp (Ideal.Quotient.mk I) with commutes' := fun _ => rfl }
  let F : S ⊗[P] A →+* Cc := (Algebra.TensorProduct.productMap fS fA).toRingHom
  have hk : I ≤ RingHom.ker (Algebra.TensorProduct.includeRight (R := P) (A := S) (B := A)).toRingHom := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : x j = algebraMap P A (X (Sum.inl j)) := by
      rw [RingHom.algebraMap_toAlgebra, hψX]; rfl
    have h2 : algebraMap P S (X (Sum.inl j)) = 0 := by
      rw [RingHom.algebraMap_toAlgebra]; exact kl j
    simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply]
    rw [h1, one_tmul_algebraMap, h2, TensorProduct.zero_tmul]
  let G : Cc →+* S ⊗[P] A :=
    eval₂Hom (Ideal.Quotient.lift I (Algebra.TensorProduct.includeRight (R := P) (A := S) (B := A)).toRingHom
      fun a ha => hk ha) fun j => X j ⊗ₜ[P] (1 : A)
  have hF1 : ∀ s : S, F (s ⊗ₜ[P] (1 : A)) = FS s := fun s => by simp [F, fS, fA]
  have hGC : ∀ a, G (C (Ideal.Quotient.mk I a)) = (1 : S) ⊗ₜ[P] a := fun a => by
    erw [MvPolynomial.eval₂Hom_C]; rfl
  have hGX : ∀ j, G (X j) = X j ⊗ₜ[P] (1 : A) := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have hFG : F.comp G = RingHom.id Cc := by
    apply MvPolynomial.ringHom_ext
    · intro r
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp [F, G, fS, fA]
    · intro j
      show F (G (X j)) = X j
      rw [hGX, hF1, hFSX]
  have hS : (G.comp F).comp (Algebra.TensorProduct.includeLeftRingHom (R := P) (A := S) (B := A)) =
      Algebra.TensorProduct.includeLeftRingHom := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r
        show G (F (C (C r) ⊗ₜ[P] (1 : A))) = C (C r) ⊗ₜ[P] (1 : A)
        have e1 : φ r = algebraMap P A (C r) := by
          rw [RingHom.algebraMap_toAlgebra]; exact (MvPolynomial.eval₂Hom_C _ _ _).symm
        have e2 : algebraMap P S (C r) = C (C r) := by
          rw [RingHom.algebraMap_toAlgebra]; exact MvPolynomial.eval₂Hom_C _ _ _
        rw [hF1, hFSC, hgC, hGC, e1, one_tmul_algebraMap, e2]
      · intro i
        show G (F (C (X i) ⊗ₜ[P] (1 : A))) = C (X i) ⊗ₜ[P] (1 : A)
        have e1 : y i = algebraMap P A (X (Sum.inr i)) := by rw [RingHom.algebraMap_toAlgebra, hψX]; rfl
        have e2 : algebraMap P S (X (Sum.inr i)) = C (X i) := by
          rw [RingHom.algebraMap_toAlgebra]; exact MvPolynomial.eval₂Hom_X' _ _ _
        rw [hF1, hFSC, hgX, hGC, e1, one_tmul_algebraMap, e2]
    · intro j
      show G (F (X j ⊗ₜ[P] (1 : A))) = X j ⊗ₜ[P] (1 : A)
      rw [hF1, hFSX, hGX]
  have hGF : G.comp F = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      have hs := RingHom.congr_fun hS s
      simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply] at hs
      have ha : G (F ((1 : S) ⊗ₜ[P] a)) = (1 : S) ⊗ₜ[P] a := by
        simp [F, G, fS, fA]; erw [MvPolynomial.eval₂Hom_C]; rfl
      have hm : s ⊗ₜ[P] a = (s ⊗ₜ[P] (1 : A)) * ((1 : S) ⊗ₜ[P] a) := by simp
      rw [RingHom.id_apply, RingHom.comp_apply, hm, map_mul, map_mul, hs, ha]
    | add u v hu hv => simp only [RingHom.comp_apply, RingHom.id_apply, map_add (f := _)] at hu hv ⊢; rw [hu, hv]
  let E : S ⊗[P] A ≃+* Cc := RingEquiv.ofRingHom F G hFG hGF
  let σ : P ≃+* S := (MvPolynomial.sumAlgEquiv R (Fin d) (Fin e)).toRingEquiv
  have s1 : ∀ r, σ (C r) = C (C r) := fun r => MvPolynomial.sumAlgEquiv_C_inl (R := R) (S₁ := Fin d) (S₂ := Fin e) r
  have s2 : ∀ j, σ (X (Sum.inl j)) = X j := fun j => MvPolynomial.sumAlgEquiv_X_inl (R := R) (S₁ := Fin d) (S₂ := Fin e) j
  have s3 : ∀ i, σ (X (Sum.inr i)) = C (X i) := fun i => MvPolynomial.sumAlgEquiv_X_inr (R := R) (S₁ := Fin d) (S₂ := Fin e) i
  have key : (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp
      ((Ideal.Quotient.mk I).comp φ)) (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i)))) =
      (E.toRingHom.comp (algebraMap S (S ⊗[P] A))).comp σ.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (C r)); rw [s1]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_C]; simp [gy]
    · rintro (j | i)
      · change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (X (Sum.inl j))); rw [s2]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_X']
      · change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (X (Sum.inr i))); rw [s3]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_C]; simp [gy]
  rw [key]
  exact RingHom.Etale.respectsIso.2 _ σ (RingHom.Etale.respectsIso.1 _ E hb)

end LateralTheory.CohomologicalPurity.LeafPolyPf
end
end
end


section
@[expose] public section

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

theorem pick_span_top (A M K : Type) [CommRing A] [AddCommGroup M] [Module A M] [Field K] [Algebra A K] :
    Submodule.span K (Set.range fun m : M => (1 : K) ⊗ₜ[A] m) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  induction v using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul k m =>
    have : k ⊗ₜ[A] m = k • ((1 : K) ⊗ₜ[A] m) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  | add a c ha hc => exact add_mem (ha trivial) (hc trivial)

theorem LeafPick_of : LeafPick := by
  intro d A M _ _ _ _ p _ hd
  set K := p.ResidueField
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent K (Set.range fun m : M => (1 : K) ⊗ₜ[A] m)
  rw [pick_span_top] at hbspan
  let B : Module.Basis b K (K ⊗[A] M) := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan])
  let _ : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = d := by rw [← hd, Module.finrank_eq_card_basis B]
  let B' := B.reindex (Fintype.equivFinOfCardEq hcard)
  have hmem : ∀ i, ∃ m : M, (1 : K) ⊗ₜ[A] m = B' i := by
    intro i
    have : B' i ∈ b := by simp [B', B]
    obtain ⟨m, hm⟩ := hbs this
    exact ⟨m, hm⟩
  choose x hx using hmem
  set N := Submodule.span A (Set.range x)
  let g : K ⊗[A] M →ₗ[K] K ⊗[A] (M ⧸ N) := (N.mkQ).baseChange K
  have hgsurj : Function.Surjective g :=
    LinearMap.lTensor_surjective K (Submodule.mkQ_surjective N)
  have hg0 : ∀ v, g v = 0 := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range B') := by rw [B'.span_eq]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨i, rfl⟩
      rw [← hx i]
      simp [g, (Submodule.Quotient.mk_eq_zero N).2 (Submodule.subset_span ⟨i, rfl⟩)]
    · simp
    · intro a c _ _ ha hc; simp [ha, hc]
    · intro r a _ ha; simp [ha]
  have hsub : Subsingleton (K ⊗[A] (M ⧸ N)) := by
    constructor; intro u w
    obtain ⟨u', rfl⟩ := hgsurj u
    obtain ⟨w', rfl⟩ := hgsurj w
    rw [hg0, hg0]
  have hnot : (⟨p, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A (M ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    intro h
    exact (not_nontrivial_iff_subsingleton.2 hsub) h
  rw [Module.mem_support_iff_of_finite] at hnot
  obtain ⟨f, hf, hfp⟩ := Set.not_subset.1 hnot
  refine ⟨x, f, hfp, fun m => ?_⟩
  rw [SetLike.mem_coe, Module.mem_annihilator] at hf
  have := hf (Submodule.Quotient.mk m)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

end LateralTheory.CohomologicalPurity.ChartCut
end
end
end


section
@[expose] public section

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

theorem chart_of_data (hS : LeafSec) {d : ℕ} {A T : Type} [CommRing A] [CommRing T] (I : Ideal A) (x : Fin d → A)
    (ι : A →+* T) (κ : MvPolynomial (Fin d) (A ⧸ I) →+* T) (μ : T →+* A ⧸ I)
    (hι : ι.Etale) (hκ : κ.Etale) (hμι : μ.comp ι = Ideal.Quotient.mk I)
    (hμκ : μ.comp κ = MvPolynomial.constantCoeff) (hx : ∀ j, ι (x j) = κ (MvPolynomial.X j))
    (hI : I = Ideal.span (Set.range x)) : Chart d A I := by
  obtain ⟨t, ht1, ht⟩ := hS A T ι I μ hι hμι
  have hu : IsUnit (algebraMap T (Localization.Away t) t) := IsLocalization.Away.algebraMap_isUnit t
  have hloc : (algebraMap T (Localization.Away t)).Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway t)
  have hμι' : ∀ a, μ (ι a) = Ideal.Quotient.mk I a := fun a => RingHom.congr_fun hμι a
  have hμκ' : ∀ q, μ (κ q) = MvPolynomial.constantCoeff q := fun q => RingHom.congr_fun hμκ q
  have key : ∀ s : T, μ s = 0 →
      algebraMap T (Localization.Away t) s ∈ I.map ((algebraMap T (Localization.Away t)).comp ι) := by
    intro s hs
    have h1 := Ideal.mem_map_of_mem (algebraMap T (Localization.Away t)) (ht s hs)
    rw [Ideal.map_map, map_mul] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h1
  have hut : IsUnit (μ t) := by rw [ht1]; exact isUnit_one
  let μB : Localization.Away t →+* A ⧸ I := IsLocalization.Away.lift t hut
  have hμB : ∀ a, μB ((algebraMap T (Localization.Away t)).comp ι a) = Ideal.Quotient.mk I a := by
    intro a
    simp only [RingHom.comp_apply, μB, IsLocalization.Away.lift_eq, hμι']
  refine ⟨Localization.Away t, inferInstance, (algebraMap T (Localization.Away t)).comp ι,
    (algebraMap T (Localization.Away t)).comp κ, ⟨RingHom.Etale.stableUnderComposition _ _ hι hloc, ?_, ?_⟩,
    RingHom.Etale.stableUnderComposition _ _ hκ hloc, ?_, ?_⟩
  · apply Ideal.quotientMap_injective'
    intro a ha
    have hker : I.map ((algebraMap T (Localization.Away t)).comp ι) ≤ RingHom.ker μB := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker, hμB, Ideal.Quotient.eq_zero_iff_mem]
      exact hb
    have := hker (Ideal.mem_comap.mp ha)
    rw [RingHom.mem_ker, hμB, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  · intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hbn⟩ := IsLocalization.surj (Submonoid.powers t) b
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (μ s)
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk]
    have e1 : Ideal.Quotient.mk (I.map ((algebraMap T (Localization.Away t)).comp ι))
        (algebraMap T (Localization.Away t) t) = 1 := by
      rw [← map_one (Ideal.Quotient.mk _)]
      refine Ideal.Quotient.eq.mpr ?_
      have := key (t - 1) (by rw [map_sub, map_one, ht1, sub_self])
      simpa [map_sub] using this
    have e2 : Ideal.Quotient.mk (I.map ((algebraMap T (Localization.Away t)).comp ι))
        (algebraMap T (Localization.Away t) s) =
        Ideal.Quotient.mk _ (((algebraMap T (Localization.Away t)).comp ι) a) := by
      refine Ideal.Quotient.eq.mpr ?_
      have := key (s - ι a) (by rw [map_sub, hμι', ha, sub_self])
      simpa [map_sub] using this
    simp only at hbn
    rw [← e2, ← hbn, map_mul, map_pow, map_pow, e1, one_pow, mul_one]
  · rw [show I.map ((algebraMap T (Localization.Away t)).comp ι) =
        (Ideal.span (Set.range x)).map ((algebraMap T (Localization.Away t)).comp ι) by rw [← hI],
      Ideal.map_span, ← Set.range_comp]
    congr 2
    funext j
    simp [hx]
  · intro a
    have := key (ι a - κ (MvPolynomial.C (Ideal.Quotient.mk I a)))
      (by rw [map_sub, hμι', hμκ', MvPolynomial.constantCoeff_C, sub_self])
    simpa [map_sub] using this

theorem chart_of_tensor (hS : LeafSec) {d : ℕ} {P A Q : Type} [CommRing P] [CommRing A] [CommRing Q] [Algebra P A]
    [Algebra P Q] (I : Ideal A) (x : Fin d → A) (c : MvPolynomial (Fin d) (A ⧸ I) ≃+* Q) [Algebra.Etale P A]
    [Algebra.Etale P Q]
    (hcomm : ∀ p, MvPolynomial.constantCoeff (c.symm (algebraMap P Q p)) = Ideal.Quotient.mk I (algebraMap P A p))
    (px : Fin d → P) (hpx1 : ∀ j, algebraMap P A (px j) = x j)
    (hpx2 : ∀ j, algebraMap P Q (px j) = c (MvPolynomial.X j))
    (hI : I = Ideal.span (Set.range x)) : Chart d A I := by
  let f : A →ₐ[P] A ⧸ I := Ideal.Quotient.mkₐ P I
  have hg : ∀ p, (MvPolynomial.constantCoeff.comp c.symm.toRingHom) (algebraMap P Q p) =
      algebraMap P (A ⧸ I) p := fun p => by
    rw [RingHom.comp_apply, ← Ideal.Quotient.mk_algebraMap]; exact hcomm p
  let g : Q →ₐ[P] A ⧸ I := { MvPolynomial.constantCoeff.comp c.symm.toRingHom with commutes' := hg }
  let μ := (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
  let ι := algebraMap A (A ⊗[P] Q)
  let κ := ((Algebra.TensorProduct.comm P Q A).toRingHom.comp (algebraMap Q (Q ⊗[P] A))).comp c.toRingHom
  have hκa : ∀ q, κ q = (1 : A) ⊗ₜ c q := fun q => by
    simp [κ, Algebra.TensorProduct.comm_tmul]
  refine chart_of_data hS I x ι κ μ (RingHom.etale_algebraMap.mpr inferInstance) ?_ ?_ ?_ ?_ hI
  · exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective c.bijective)
      (RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.mpr inferInstance)
        (RingHom.Etale.of_bijective (Algebra.TensorProduct.comm P Q A).bijective))
  · ext a; simp [μ, ι, f, g]
  · apply RingHom.ext; intro q; simp [μ, hκa, f, g]
  · intro j
    rw [hκa]
    show x j ⊗ₜ 1 = _
    rw [← hpx1, ← hpx2, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := Q),
      TensorProduct.smul_tmul]

theorem LeafNbhd_of (hS : LeafSec) (hP : LeafPoly) : LeafNbhd := by
  intro e d R A _ _ φ I x y hc
  have hπ := hP e d R A φ I x y hc
  set α := MvPolynomial.eval₂Hom φ (Sum.elim x y) with hα
  set π := (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp
    ((Ideal.Quotient.mk I).comp φ)) (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i))))
    with hπdef
  have hxI : ∀ j, x j ∈ I := fun j => hc.2 ▸ Ideal.subset_span ⟨j, rfl⟩
  have hcomm : MvPolynomial.constantCoeff.comp π = (Ideal.Quotient.mk I).comp α := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [π, α]
    · intro i
      rcases i with j | i
      · simp [π, α, Ideal.Quotient.eq_zero_iff_mem.mpr (hxI j)]
      · simp [π, α]
  exact @chart_of_tensor hS d _ A _ _ _ _ α.toAlgebra π.toAlgebra I x (RingEquiv.refl _) hc.1.toAlgebra hπ.toAlgebra
    (fun p => RingHom.congr_fun hcomm p) (fun j => MvPolynomial.X (Sum.inl j)) (fun j => by show α _ = x j; rw [hα]; simp)
    (fun j => by show π _ = _; rw [hπdef]; simp) hc.2

end LateralTheory.CohomologicalPurity.ChartCut
end
end
end


section
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.ChartCut

theorem LeafLoc_of : LeafLoc := by
  intro d P x W hxW
  have := P.cl; have := P.smX; have := P.smZ
  obtain ⟨T, hT, hxT, -⟩ := exists_isAffineOpen_mem_and_subset (x := P.p.base x) (U := ⊤) trivial
  obtain ⟨V, hV, hxV, hVW⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := W ⊓ P.p ⁻¹ᵁ T) ⟨hxW, hxT⟩
  have e : V ≤ P.p ⁻¹ᵁ T := fun y hy => (hVW hy).2
  refine ⟨⟨V, hV⟩, hxV, fun y hy => (hVW hy).1, Γ(P.S, T), inferInstance, (P.p.appLE T V e).hom, ?_, ?_⟩
  · exact HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension (P.e + d)) P.p P.smX ⟨T, hT⟩ ⟨V, hV⟩ e
  · have hV' : IsAffineOpen (P.ι ⁻¹ᵁ V) := hV.preimage P.ι
    have e2 : P.ι ⁻¹ᵁ V ≤ (P.ι ≫ P.p) ⁻¹ᵁ T := fun y hy => e hy
    have h2 := HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension P.e) (P.ι ≫ P.p) P.smZ
      ⟨T, hT⟩ ⟨P.ι ⁻¹ᵁ V, hV'⟩ e2
    have hc : (P.ι ≫ P.p).appLE T (P.ι ⁻¹ᵁ V) e2 = P.p.appLE T V e ≫ P.ι.app V := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    rw [hc] at h2
    have hs : Function.Surjective (P.ι.app V).hom := P.ι.app_surjective V hV
    have hk : P.ι.ker.ideal ⟨V, hV⟩ = RingHom.ker (P.ι.app V).hom := P.ι.ker_apply ⟨V, hV⟩
    rw [hk]
    let eqv := RingHom.quotientKerEquivOfSurjective hs
    have heq : (Ideal.Quotient.mk (RingHom.ker (P.ι.app V).hom)).comp (P.p.appLE T V e).hom =
        eqv.symm.toRingHom.comp ((P.p.appLE T V e ≫ P.ι.app V).hom) := by
      ext a
      simp only [RingHom.comp_apply, CommRingCat.hom_comp]
      apply eqv.injective
      simp [eqv]
    rw [heq]
    exact (RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).left _ _ h2

end LateralTheory.CohomologicalPurity.ChartCut
end
end
end


section
@[expose] public section

noncomputable section
open TensorProduct KaehlerDifferential

namespace LateralTheory.CohomologicalPurity.LeafEtPf

theorem etale_main (n : ℕ) (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] (z : ι → A)
    (hn : Fintype.card ι = n) (hA : Algebra.IsStandardSmoothOfRelativeDimension n R A)
    (hspan : Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (z k)) = ⊤) :
    (MvPolynomial.eval₂Hom (algebraMap R A) z).Etale := by
  rcases subsingleton_or_nontrivial A with hA0 | hA0
  · exact ChartCut.etale_of_subsingleton _
  letI : Algebra (MvPolynomial ι R) A := (MvPolynomial.aeval z).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial ι R) A :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.aeval_C z r).symm
  have := hA
  have : Algebra.IsStandardSmooth R A := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have hD : ∀ k, mapBaseChange R (MvPolynomial ι R) A
      ((1 : A) ⊗ₜ D R (MvPolynomial ι R) (MvPolynomial.X k)) = D R A (z k) := by
    intro k
    rw [mapBaseChange_tmul, one_smul, map_D]
    congr 1
    exact MvPolynomial.aeval_X z k
  have hsurj : Function.Surjective (mapBaseChange R (MvPolynomial ι R) A) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, hD k⟩
  haveI hΩ : Subsingleton Ω[A⁄MvPolynomial ι R] := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    obtain ⟨w, rfl⟩ := map_surjective R (MvPolynomial ι R) A ω
    obtain ⟨u, rfl⟩ := hsurj w
    exact (exact_mapBaseChange_map R (MvPolynomial ι R) A).apply_apply_eq_zero u
  have hfin : Module.finrank A Ω[A⁄R] = n :=
    Module.finrank_eq_of_rank_eq (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)
  let b := Algebra.TensorProduct.basis A (mvPolynomialBasis R ι)
  have hli : LinearIndependent A (mapBaseChange R (MvPolynomial ι R) A ∘ b) := by
    have : (mapBaseChange R (MvPolynomial ι R) A ∘ b) = fun k => D R A (z k) := by
      funext k
      simp only [Function.comp_apply, b, Algebra.TensorProduct.basis_apply, mvPolynomialBasis_apply, hD]
    rw [this]
    exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (hn.trans hfin.symm)
  have hinj : Function.Injective (mapBaseChange R (MvPolynomial ι R) A) :=
    LinearMap.injective_of_linearIndependent b.span_eq hli
  haveI hH1 : Subsingleton (Algebra.H1Cotangent (MvPolynomial ι R) A) := by
    refine subsingleton_of_forall_eq 0 fun h => ?_
    have h1 : Algebra.H1Cotangent.δ R (MvPolynomial ι R) A h = 0 := by
      apply hinj
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R (MvPolynomial ι R) A).apply_apply_eq_zero h
    obtain ⟨g, rfl⟩ := ((Algebra.H1Cotangent.exact_map_δ R (MvPolynomial ι R) A) h).mp h1
    rw [Subsingleton.elim g 0, map_zero]
  have : Algebra.FinitePresentation (MvPolynomial ι R) A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial ι R) A
  have : Algebra.IsStandardSmooth (MvPolynomial ι R) A :=
    Algebra.IsStandardSmooth.of_basis_kaehlerDifferential (I := Empty) (Module.Basis.empty _) (by rintro _ ⟨i, _⟩; exact i.elim)
  have : Algebra.FormallyUnramified (MvPolynomial ι R) A := ⟨hΩ⟩
  have : Algebra.Etale (MvPolynomial ι R) A :=
    Algebra.Etale.iff_formallyUnramified_and_smooth.mpr ⟨inferInstance, inferInstance⟩
  exact RingHom.etale_algebraMap.mpr this

theorem LeafEt_of : ChartCut.LeafEt := by
  intro n R A ι _ _ _ _ z hn hA hspan
  exact etale_main n R A ι z hn hA hspan

end LateralTheory.CohomologicalPurity.LeafEtPf
end
end
end


section
@[expose] public section

noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

lemma kd_span {R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra A A']
    [Algebra R A'] [IsScalarTower R A A'] (f : A) [IsLocalization.Away f A'] (N : Submodule A' Ω[A'⁄R])
    (hN : ∀ a : A, KaehlerDifferential.D R A' (algebraMap A A' a) ∈ N) : N = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨a', rfl⟩
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) a'
  simp only at hs
  have hu : IsUnit (algebraMap A A' (s : A)) := IsLocalization.map_units A' s
  have h1 : algebraMap A A' (s : A) • KaehlerDifferential.D R A' a' ∈ N := by
    have h := congrArg (KaehlerDifferential.D R A') hs
    rw [Derivation.leibniz] at h
    have e : algebraMap A A' (s : A) • KaehlerDifferential.D R A' a' =
        KaehlerDifferential.D R A' (algebraMap A A' a) - a' • KaehlerDifferential.D R A' (algebraMap A A' s) := by
      rw [← h]; abel
    rw [e]; exact N.sub_mem (hN a) (N.smul_mem _ (hN s))
  obtain ⟨u, hu'⟩ := hu
  have h2 := N.smul_mem (↑u⁻¹ : A') h1
  rwa [← hu', smul_smul, Units.inv_mul, one_smul] at h2

theorem LeafCoord_of (hR : LeafRank) (hP : LeafPick) (hS : LeafSpan) (hE : LeafEt) : LeafCoord := by
  intro e d R A _ _ φ I p hp hIp hstd
  letI : Algebra R A := φ.toAlgebra
  haveI h1 : Algebra.IsStandardSmoothOfRelativeDimension (e + d) R A := hstd.1
  haveI h2 : Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) := hstd.2
  haveI : Algebra.IsStandardSmooth R A := h1.isStandardSmooth
  haveI : Algebra.IsStandardSmooth R (A ⧸ I) := h2.isStandardSmooth
  have hfg : I.FG := by
    have := Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ_surjective R I)
    simpa [Ideal.Quotient.mkₐ_ker] using this
  haveI : Module.Finite A I := Module.Finite.iff_fg.mpr hfg
  haveI := hp
  have hrank := hR e d R A I p hIp h1 h2
  obtain ⟨x, f, hf, hx⟩ := hP d A I p hrank
  set x' : Fin d → A := fun j => (x j : A) with hx'
  have hxI : ∀ j, x' j ∈ I := fun j => (x j).2
  have hfx : ∀ a ∈ I, f * a ∈ Ideal.span (Set.range x') := by
    intro a ha
    have h := Submodule.mem_map_of_mem (f := I.subtype) (hx ⟨a, ha⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  obtain ⟨y, g, hg, hy⟩ := hS e d R A I p hp hIp h2 x' f hxI hf hfx
  refine ⟨f * g, fun h => (hp.mem_or_mem h).elim hf hg, ?_⟩
  intro A' _ _ _
  letI : Algebra R A' := ((algebraMap A A').comp φ).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hfgu : IsUnit (algebraMap A A' (f * g)) := IsLocalization.Away.algebraMap_isUnit (f * g)
  rw [map_mul] at hfgu
  have hfu : IsUnit (algebraMap A A' f) := isUnit_of_mul_isUnit_left hfgu
  have hgu : IsUnit (algebraMap A A' g) := isUnit_of_mul_isUnit_right hfgu
  refine ⟨fun j => algebraMap A A' (x' j), fun k => algebraMap A A' (y k), ?_, ?_⟩
  · haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 A A' :=
      Algebra.IsStandardSmoothOfRelativeDimension.localization_away (f * g)
    have h3 : Algebra.IsStandardSmoothOfRelativeDimension (0 + (e + d)) R A' :=
      Algebra.IsStandardSmoothOfRelativeDimension.trans (R := R) (S := A) (T := A') (n := e + d) (m := 0)
    rw [zero_add] at h3
    refine hE (e + d) R A' (Fin d ⊕ Fin e) _ (by simp [add_comm]) h3 ?_
    apply kd_span (R := R) (A := A) (f * g)
    intro a
    have hm := Submodule.mem_map_of_mem (f := KaehlerDifferential.map R R A A')
      (hy (KaehlerDifferential.D R A a))
    rw [Submodule.map_span, LinearMap.map_smul, KaehlerDifferential.map_D] at hm
    have hle : Submodule.span A (KaehlerDifferential.map R R A A' ''
        Set.range fun k => KaehlerDifferential.D R A (Sum.elim x' y k)) ≤
        (Submodule.span A' (Set.range fun k => KaehlerDifferential.D R A'
          (Sum.elim (fun j => algebraMap A A' (x' j)) (fun k => algebraMap A A' (y k)) k))).restrictScalars A := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      rw [KaehlerDifferential.map_D]
      apply Submodule.subset_span
      exact ⟨k, by cases k <;> rfl⟩
    have h5 := hle hm
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul A'] at h5
    obtain ⟨u, hu⟩ := hgu
    have h6 := Submodule.smul_mem _ (↑u⁻¹ : A') h5
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h6
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      have h := Ideal.mem_map_of_mem (algebraMap A A') (hfx a ha)
      rw [Ideal.map_span, map_mul, ← Set.range_comp] at h
      obtain ⟨u, hu⟩ := hfu
      have h6 := Ideal.mul_mem_left _ (↑u⁻¹ : A') h
      rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at h6
      exact h6
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.mem_map_of_mem _ (hxI j)

end LateralTheory.CohomologicalPurity.ChartCut
end
end
end


@[expose] public section

namespace LateralTheory.Fin.LeafChart

alias etale_chart_localization_property_holds := _root_.LateralTheory.CohomologicalPurity.ChartCut.LeafLoc_of
alias etale_chart_shrinking_open_property_holds := _root_.LateralTheory.CohomologicalPurity.ChartCut.LeafShrink_of
alias etale_chart_conormal_rank_property_holds := _root_.LateralTheory.CohomologicalPurity.ChartCut.LeafRank_of
alias etale_chart_generator_choice_property_holds := _root_.LateralTheory.CohomologicalPurity.ChartCut.LeafPick_of
alias etale_chart_ideal_span_property_holds := _root_.LateralTheory.CohomologicalPurity.LeafSpanPf.LeafSpan_of
alias etale_chart_etaleness_property_holds := _root_.LateralTheory.CohomologicalPurity.LeafEtPf.LeafEt_of

theorem etale_chart_coordinate_functions_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafCoord :=
  LateralTheory.CohomologicalPurity.ChartCut.LeafCoord_of
    etale_chart_conormal_rank_property_holds
    etale_chart_generator_choice_property_holds
    etale_chart_ideal_span_property_holds
    etale_chart_etaleness_property_holds

alias etale_chart_section_property_holds := _root_.LateralTheory.CohomologicalPurity.LeafSecPf.LeafSec_of
alias etale_chart_polynomial_algebra_property_holds := _root_.LateralTheory.CohomologicalPurity.LeafPolyPf.leafPoly

theorem etale_chart_neighborhood_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd :=
  LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd_of
    etale_chart_section_property_holds
    etale_chart_polynomial_algebra_property_holds

theorem etale_coordinate_chart_existence : LateralTheory.CohomologicalPurity.LeafChart :=
  LateralTheory.CohomologicalPurity.ChartCut.goal_of
    etale_chart_localization_property_holds
    etale_chart_shrinking_open_property_holds
    etale_chart_coordinate_functions_property_holds
    etale_chart_neighborhood_property_holds

alias intersectionNumber_baseChange := _root_.LateralTheory.Fin.LeafChart.etale_coordinate_chart_existence

end LateralTheory.Fin.LeafChart
