module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
public import Formalism.HermitianLattices.StatementMass
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.Complex
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStA
import ReciprocityTheory.SemistableReduction.SemiDegC

@[expose] public section

open MeasureTheory Module NumberField Matrix Finset Formalism.HermitianLatticesTheory
open ReciprocityTheory.MultiplicativeHeights
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.ShortVec

theorem denseRange_emb {K : Type} [Field K] (σ : K →+* ℂ) (h : ¬ ComplexEmbedding.IsReal σ) :
    DenseRange σ :=
  GlobalTheory.SlopeExt.denseRange_of_not_isReal h

private theorem posDef_map {K : Type} [Field K] [StarRing K] {n : ℕ} (σ : K →+* ℂ)
    (hσ : ¬ ComplexEmbedding.IsReal σ) (hs : ∀ a, σ (star a) = starRingEnd ℂ (σ a))
    (G : Matrix (Fin n) (Fin n) K) (hG : Gᴴ = G)
    (h : ∀ y : Fin n → K, y ≠ 0 → 0 < (σ (star y ⬝ᵥ (G *ᵥ y))).re) : (G.map σ).PosDef := by
  have hH : (G.map σ).IsHermitian := by
    ext i j
    simp only [conjTranspose_apply, map_apply]
    rw [Complex.star_def, ← hs, ← conjTranspose_apply, hG]
  have hnn : ∀ y : Fin n → K, 0 ≤ star (fun i => σ (y i)) ⬝ᵥ (G.map σ *ᵥ fun i => σ (y i)) := by
    intro y
    have hqv : star (fun i => σ (y i)) ⬝ᵥ (G.map σ *ᵥ fun i => σ (y i)) = σ (star y ⬝ᵥ (G *ᵥ y)) := by
      simp [dotProduct, mulVec, map_sum, map_mul, hs]
    rw [Complex.le_def]
    refine ⟨?_, by simpa using (hH.im_star_dotProduct_mulVec_self _).symm⟩
    rw [hqv]
    by_cases hy : y = 0
    · simp [hy]
    · simpa using (h y hy).le
  have hpsd : ∀ w : Fin n → ℂ, 0 ≤ star w ⬝ᵥ (G.map σ *ᵥ w) := fun w =>
    (DenseRange.piMap fun _ : Fin n => denseRange_emb σ hσ).induction_on w
      (isClosed_le continuous_const (by simp only [dotProduct, mulVec]; fun_prop)) hnn
  refine PosDef.of_dotProduct_mulVec_pos hH fun w hw => lt_of_le_of_ne (hpsd w) fun h0 => ?_
  have hk := (PosSemidef.of_dotProduct_mulVec_nonneg hH hpsd).dotProduct_mulVec_zero_iff.1 h0.symm
  have hdσ : σ G.det = 0 := by rw [RingHom.map_det]; exact exists_mulVec_eq_zero_iff.1 ⟨w, hw, hk⟩
  obtain ⟨y, hy, hGy⟩ := exists_mulVec_eq_zero_iff.2 ((map_eq_zero σ).1 hdσ)
  have := h y hy
  simp [hGy] at this

private theorem ellipsoid_props_and_volume {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef)
    {R : ℝ} (hR : 0 < R) :
    let E := {u : Fin 2 → ℂ | (star u ⬝ᵥ (G *ᵥ u)).re ≤ R ^ 2}
    Convex ℝ E ∧ (∀ u ∈ E, -u ∈ E) ∧
      volume E = ENNReal.ofReal (Real.pi ^ 2 / 2 * (R ^ 2) ^ 2 / G.det.re) := by
  intro E
  let B : Matrix (Fin 2) (Fin 2) ℂ := CFC.sqrt G
  have hBG : Bᴴ * B = G := by
    change star B * B = G
    rw [(CFC.sqrt_nonneg G).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  let L : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ) := (Matrix.toLin' B).restrictScalars ℝ
  let Ball : Set (Fin 2 → ℂ) := {z : Fin 2 → ℂ | ∑ i, ‖z i‖ ^ 2 ≤ R ^ 2}
  have hE : E = L ⁻¹' Ball := by
    ext u
    simp only [E, Ball, Set.mem_ofPred_eq, Set.mem_preimage, L, LinearMap.coe_restrictScalars,
      Matrix.toLin'_apply]
    suffices (star u ⬝ᵥ (G *ᵥ u)).re = ∑ i, ‖(B *ᵥ u) i‖ ^ 2 by rw [this]
    rw [← hBG, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
    simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.sq_norm]
  have hBall_eq : Ball = (WithLp.linearEquiv 2 ℝ (Fin 2 → ℂ)).symm ⁻¹'
      Metric.closedBall (0 : EuclideanSpace ℂ (Fin 2)) R := by
    ext z
    simp only [Ball, Set.mem_ofPred_eq, Set.mem_preimage, mem_closedBall_zero_iff,
      WithLp.linearEquiv_symm_apply, EuclideanSpace.norm_eq, Real.sqrt_le_left hR.le]
    rfl
  have hΔpos : 0 < G.det.re := (Complex.lt_def.1 hG.det_pos).1
  have hLdet : LinearMap.det L = G.det.re := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      ← hBG, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have hvol_ball : volume Ball = ENNReal.ofReal (Real.pi ^ 2 / 2 * (R ^ 2) ^ 2) := by
    have hBall_rpow : Ball = {z : Fin 2 → ℂ | (∑ i, ‖z i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ R} := by
      ext z; simp only [Ball, Set.mem_ofPred_eq, Real.rpow_two, ← Real.sqrt_eq_rpow,
        Real.sqrt_le_left hR.le]
    have hΓ2 : Real.Gamma (2 / 2 + 1) = 1 := by norm_num [Real.Gamma_two]
    have hΓ3 : Real.Gamma (2 * 2 / 2 + 1) = 2 := by
      rw [show (2 * 2 / 2 + 1 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
      norm_num
    rw [hBall_rpow, Complex.volume_sum_rpow_le (Fin 2) (by norm_num : (1 : ℝ) ≤ 2) R]
    simp only [Fintype.card_fin, Nat.cast_ofNat, hΓ2, hΓ3]
    rw [← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  refine ⟨?_, fun u hu => by simpa [E, star_neg, mulVec_neg] using hu, ?_⟩
  · rw [hE, hBall_eq]
    exact ((convex_closedBall 0 R).linear_preimage
      (WithLp.linearEquiv 2 ℝ (Fin 2 → ℂ)).symm.toLinearMap).linear_preimage L
  · rw [hE, Measure.addHaar_preimage_linearMap volume (by rw [hLdet]; exact hΔpos.ne'), hLdet,
      hvol_ball, abs_of_pos (inv_pos.2 hΔpos), ← ENNReal.ofReal_mul (inv_nonneg.2 hΔpos.le)]
    congr 1; ring

theorem exists_short_vector : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (J : Matrix (Fin 2) (Fin 2) E), Jᴴ = J → (∀ (φ : E →+* ℂ) (y : Fin 2 → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (J *ᵥ y))).re) → ∀ Λ : Submodule (𝓞 E) (Fin 2 → E), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → ∃ u ∈ Λ, u ≠ 0 ∧ ∀ φ : E →+* ℂ, (φ (star u ⬝ᵥ (J *ᵥ u))).re ≤ 2 * Formalism.HermitianLatticesTheory.vInv E := by
  intro E _ _ _ hCM J hJ hp Λ hΛ hdual
  classical
  have : IsTotallyComplex E := hCM.1
  have hs := hCM.2.1
  have hfg : Λ.FG := hΛ.fg
  -- Step 1: Λ spans E² over E, hence contains an E-basis v : Fin 2 → (Fin 2 → E).
  have hspan : Submodule.span E (Λ : Set (Fin 2 → E)) = ⊤ := by
    by_contra hspan
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
    have hinj : Function.Injective J.mulVecLin := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      by_contra hx0
      obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have ht := hp σ x hx0
      change J *ᵥ x = 0 at hx
      simp [hx] at ht
    obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hinj) fun i => star (φ (Pi.single i 1))
    have hpair (y : Fin 2 → E) : star y ⬝ᵥ (J *ᵥ u) = star (φ y) := by
      change J *ᵥ u = _ at hu
      rw [hu, dotProduct, φ.pi_apply_eq_sum_univ y, star_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, star_mul, mul_comm, Pi.star_apply]
      congr 3
      ext j
      simp [Pi.single_apply, eq_comm]
    have hu0 : u ≠ 0 := fun h0 => hφ0 <| LinearMap.ext fun y => by
      have := hpair y; simp [h0] at this; exact star_eq_zero.mp this.symm
    have hline (a : E) : a • u ∈ Λ := (hdual _).2 fun y hy => by
      have hy0 : φ y = 0 := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
      rw [mulVec_smul, dotProduct_smul, hpair, hy0]; simp
    let i : E →ₗ[𝓞 E] Λ :=
      ((LinearMap.toSpanSingleton E _ u).restrictScalars (𝓞 E)).codRestrict Λ hline
    have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
    have : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E hu0 (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨s, hsΛ, hs_span, hs_li⟩ := exists_linearIndependent E (Λ : Set (Fin 2 → E))
  let b_s : Basis s E (Fin 2 → E) := Basis.mk hs_li
    (by rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hs_span, hspan])
  let : Fintype s := FiniteDimensional.fintypeBasisIndex b_s
  let e_s : s ≃ Fin 2 :=
    Fintype.equivFinOfCardEq (by rw [← Module.finrank_eq_card_basis b_s, Module.finrank_fin_fun])
  let b_v : Basis (Fin 2) E (Fin 2 → E) := b_s.reindex e_s
  let v : Fin 2 → (Fin 2 → E) := b_v
  have hvΛ : ∀ i, v i ∈ Λ := fun i => by
    rw [show v i = b_s (e_s.symm i) from Basis.reindex_apply b_s e_s i, Basis.mk_apply]
    exact hsΛ (e_s.symm i).2
  have hb : IsKBasisIn Λ v := ⟨hvΛ, b_v.linearIndependent, fun x _ => by rw [b_v.span_eq]; trivial⟩
  -- Step 2: Gram matrix G of v is positive-definite at every complex embedding, and |N(det G)| ≤ n².
  let S : HermForm E 2 :=
    { c := starRingEnd E, c_invol := star_star, c_emb := hs, G := J,
      G_herm := fun a b => by simpa [conjTranspose_apply, starRingEnd_apply] using congrFun (congrFun hJ b) a }
  have hSh : ∀ x y, S.h x y = star x ⬝ᵥ (J *ᵥ y) := fun x y => by
    simp [HermForm.h, S, dotProduct, mulVec, mul_add, mul_assoc, starRingEnd_apply]
  have hsd : IsSelfDual S Λ := by
    refine ⟨fun x hx y hy => ?_, fun x hx => (hdual x).2 fun y hy => ?_⟩
    · obtain ⟨w, hw⟩ := (hdual y).1 hy x hx; exact ⟨w, by rw [hSh]; exact hw⟩
    · obtain ⟨w, hw⟩ := hx y hy
      have e : star (S.h x y) = star y ⬝ᵥ (J *ᵥ x) := by
        rw [hSh, star_dotProduct, star_mulVec, star_star, hJ, ← dotProduct_mulVec]
      rw [← e, ← hw]; exact ⟨⟨star (w : E), w.2.map (starRingEnd E).toIntAlgHom⟩, rfl⟩
  let Λc := SemiDegIdx.coordLat Λ v
  have hle_Λc : SemiDegIdx.intVec E 2 ≤ Λc := SemiDegIdx.intVec_le_coordLat hb
  set G : Matrix (Fin 2) (Fin 2) E := hGram S v
  have hGH : Gᴴ = G := by
    ext i j; simp only [G, hGram, conjTranspose_apply, Matrix.of_apply, hSh]
    rw [star_dotProduct, star_mulVec, star_star, hJ, ← dotProduct_mulVec]
  have hcomb_eq : ∀ c : Fin 2 → E,
      star c ⬝ᵥ (G *ᵥ c) = star (SemiDegIdx.combMap v c) ⬝ᵥ (J *ᵥ SemiDegIdx.combMap v c) := fun c => by
    rw [← hSh, SemiDegIdx.coordForm_h]
    simp [SemiDegIdx.coordForm, HermForm.h, S, G, dotProduct, mulVec, mul_assoc, starRingEnd_apply]
    ring
  have hGpos : ∀ σ : E →+* ℂ, (G.map σ).PosDef := fun σ =>
    posDef_map σ (IsTotallyComplex.complexEmbedding_not_isReal σ) (hs σ) G hGH fun c hc => by
      rw [hcomb_eq c]
      exact hp σ _ fun h0 => hc (SemiDegIdx.combMap_injective hb.2.1 (by simpa using h0))
  set n : ℕ := SemiDegIdx.vecIdx Λc
  have hbound : ((|Algebra.norm ℚ G.det| : ℚ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast SemiDegIdx.vec_selfDual_bound (SemiDegIdx.coordForm S v) Λc
      (SemiDegIdx.coordLat_fg hfg hb) hle_Λc (SemiDegIdx.coordLat_selfDual hb hsd)
  set f := InfinitePlace.nrComplexPlaces E
  have hf : 0 < f := by have := IsTotallyComplex.finrank E; have := Module.finrank_pos (R := ℚ) (M := E); lia
  have hdetpos : ∀ σ : E →+* ℂ, 0 < (G.map σ).det.re := fun σ => (Complex.lt_def.1 (hGpos σ).det_pos).1
  set P : ℝ := ∏ w : {w : InfinitePlace E // w.IsComplex}, (G.map w.1.embedding).det.re
  have hP : 0 < P := Finset.prod_pos fun w _ => hdetpos _
  have hPn : P ≤ (n : ℝ) := by
    have hnorm : ∀ σ : E →+* ℂ, ‖σ G.det‖ = (G.map σ).det.re := fun σ => by
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
      obtain ⟨h1, h2⟩ := Complex.lt_def.1 (hGpos σ).det_pos
      have e : (G.map σ).det = ((G.map σ).det.re : ℂ) := Complex.ext rfl (by simp at h2 ⊢; linarith)
      conv_lhs => rw [e]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1]
    have hP2 : P ^ 2 = ((|Algebra.norm ℚ G.det| : ℚ) : ℝ) := by
      rw [← InfinitePlace.prod_eq_abs_norm, ← Finset.prod_pow]
      refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w) _ _ fun w => ?_
      show (G.map w.1.embedding).det.re ^ 2 = w.1 G.det ^ InfinitePlace.mult w.1
      rw [InfinitePlace.mult_isComplex w, ← hnorm, InfinitePlace.norm_embedding_eq]
    nlinarith [hP, hbound, hP2, Nat.cast_nonneg (α := ℝ) n]
  have hn : (0 : ℝ) < n := hP.trans_le hPn
  -- Step 3: Embed Λc into ({w // w.IsComplex} → Fin 2 → ℂ) and compute its covolume.
  have : IsEmpty {w : InfinitePlace E // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩
  let emb : (Fin 2 → E) →+ ({w : InfinitePlace E // w.IsComplex} → Fin 2 → ℂ) :=
    { toFun := fun c w i => w.1.embedding (c i)
      map_zero' := by ext w i; simp
      map_add' := fun x y => by ext w i; simp [Pi.add_apply] }
  have hemb_inj : Function.Injective emb := fun x y hxy => by
    obtain ⟨w⟩ := Fintype.card_pos_iff.1 hf
    exact funext fun i => w.1.embedding.injective (congrFun (congrFun hxy w) i)
  let eW : (Fin 2 → mixedEmbedding.mixedSpace E) ≃ₗ[ℝ]
      ({w : InfinitePlace E // w.IsComplex} → Fin 2 → ℂ) :=
    { toFun := fun y w i => (y i).2 w
      invFun := fun z i => (IsEmpty.elim ‹_›, fun w => z w i)
      left_inv := fun y => by ext i w; exact IsEmpty.elim ‹_› w; rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmp_eW : MeasurePreserving eW volume volume := by
    have : IsProbabilityMeasure (volume : Measure ({w : InfinitePlace E // w.IsReal} → ℝ)) :=
      ⟨by change Measure.pi (fun _ => volume) Set.univ = 1; rw [Measure.pi_univ]
          exact Finset.prod_eq_one fun w _ => IsEmpty.elim ‹_› w⟩
    have h1 := MeasureTheory.measurePreserving_pi _ _ fun _ : Fin 2 =>
      (MeasureTheory.measurePreserving_snd (μ := (volume : Measure ({w : InfinitePlace E // w.IsReal} → ℝ)))
        (ν := (volume : Measure ({w : InfinitePlace E // w.IsComplex} → ℂ))))
    have h2 := MeasureTheory.volume_preserving_finTwoArrow ({w : InfinitePlace E // w.IsComplex} → ℂ)
    have h3 := (MeasureTheory.volume_measurePreserving_arrowProdEquivProdArrow ℂ ℂ
      {w : InfinitePlace E // w.IsComplex}).symm
    have h4 := MeasureTheory.measurePreserving_pi _ _ fun _ : {w : InfinitePlace E // w.IsComplex} =>
      (MeasureTheory.volume_preserving_finTwoArrow ℂ).symm
    convert h4.comp (h3.comp (h2.comp h1)) using 1
    ext y w i
    fin_cases i <;> rfl
  let B₀ : Basis (Σ _ : Fin 2, Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ
      ({w : InfinitePlace E // w.IsComplex} → Fin 2 → ℂ) :=
    (Pi.basis fun _ : Fin 2 => mixedEmbedding.latticeBasis E).map eW
  let L₀ : Submodule ℤ ({w : InfinitePlace E // w.IsComplex} → Fin 2 → ℂ) :=
    Submodule.span ℤ (Set.range B₀)
  have hL₀_eq : L₀.toAddSubgroup = (SemiDegIdx.intVec E 2).toAddSubgroup.map emb := by
    ext y
    simp only [L₀, Submodule.mem_toAddSubgroup, Basis.mem_span_iff_repr_mem ℤ B₀, B₀,
      Basis.map_repr, LinearEquiv.trans_apply, Pi.basis_repr, Sigma.forall, AddSubgroup.mem_map]
    constructor
    · intro h
      have h' : ∀ i, ∃ a : 𝓞 E, mixedEmbedding E (a : E) = eW.symm y i := fun i => by
        have hi := (Basis.mem_span_iff_repr_mem ℤ (mixedEmbedding.latticeBasis E) _).2 (h i)
        rw [mixedEmbedding.mem_span_latticeBasis] at hi
        simpa [LinearMap.mem_range] using hi
      choose a ha using h'
      refine ⟨fun i => (a i : E), SemiDegIdx.mem_intVec.2 fun i => Submodule.mem_one.2 ⟨a i, rfl⟩, ?_⟩
      ext w i; simpa [emb, mixedEmbedding, eW] using congrArg (fun p : mixedEmbedding.mixedSpace E => p.2 w) (ha i)
    · rintro ⟨c, hc, rfl⟩ i k
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 (SemiDegIdx.mem_intVec.1 hc i)
      have he : eW.symm (emb c) i = mixedEmbedding E (a : E) := by
        ext w; · exact IsEmpty.elim ‹_› w
        · simp [eW, emb, mixedEmbedding, ha]
      rw [he]
      exact (Basis.mem_span_iff_repr_mem ℤ (mixedEmbedding.latticeBasis E) _).1
        ((mixedEmbedding.mem_span_latticeBasis E).2 ⟨a, rfl⟩) k
  let L : Submodule ℤ ({w : InfinitePlace E // w.IsComplex} → Fin 2 → ℂ) :=
    (Λc.toAddSubgroup.map emb).toIntSubmodule
  have hL₀L : L₀ ≤ L := fun y hy => by
    change y ∈ Λc.toAddSubgroup.map emb
    rw [← Submodule.mem_toAddSubgroup, hL₀_eq] at hy
    exact AddSubgroup.map_mono (fun x hx => hle_Λc hx) hy
  have : DiscreteTopology L₀ := by unfold L₀; infer_instance
  have : IsZLattice ℝ L₀ := by unfold L₀; infer_instance
  have : DiscreteTopology L := by
    have hmem : ∀ y ∈ L, n • y ∈ L₀ := fun y ⟨x, hx, hxy⟩ => by
      change n • y ∈ L₀.toAddSubgroup
      rw [← hxy, hL₀_eq, ← map_nsmul]
      exact AddSubgroup.mem_map_of_mem _ (AddSubgroup.nsmul_relIndex_mem _ hx)
    refine DiscreteTopology.of_continuous_injective
      (f := fun y : L => (⟨n • (y : {w : InfinitePlace E // w.IsComplex} → Fin 2 → ℂ), hmem y y.2⟩ : L₀))
      (Continuous.subtype_mk ((continuous_const_smul n).comp continuous_subtypeVal) _) fun a b hab => ?_
    have h1 : (n : ℝ) • (a : {w : InfinitePlace E // w.IsComplex} → Fin 2 → ℂ) =
        (n : ℝ) • (b : {w : InfinitePlace E // w.IsComplex} → Fin 2 → ℂ) := by
      simpa only [Nat.cast_smul_eq_nsmul] using congrArg Subtype.val hab
    exact Subtype.ext (smul_right_injective _ hn.ne' h1)
  have : IsZLattice ℝ L :=
    ⟨by rw [eq_top_iff, ← IsZLattice.span_top (L := L₀)]; exact Submodule.span_mono hL₀L⟩
  have : (volume : Measure ({w : InfinitePlace E // w.IsComplex} → Fin 2 → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  set D : ℝ := |(discr E : ℝ)|
  have hD : 0 < D := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero E))
  have hcovL₀ : ZLattice.covolume L₀ volume = ((2 : ℝ)⁻¹ ^ f * Real.sqrt D) ^ 2 := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L₀ volume (ZSpan.isAddFundamentalDomain B₀ volume)]
    have hFD : ZSpan.fundamentalDomain B₀ = eW '' (Set.univ.pi fun _ : Fin 2 =>
        ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis E)) := by
      ext y
      simp only [ZSpan.mem_fundamentalDomain, B₀, Basis.map_repr, LinearEquiv.trans_apply,
        Pi.basis_repr, Sigma.forall, Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies]
      exact ⟨fun h => ⟨eW.symm y, h, eW.apply_symm_apply y⟩, fun ⟨x, hx, hxy⟩ => by simpa [← hxy] using hx⟩
    have hmp_symm : MeasurePreserving eW.symm volume volume :=
      hmp_eW.symm eW.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
    rw [hFD, measureReal_def, eW.image_eq_preimage_symm,
      hmp_symm.measure_preimage
        (MeasurableSet.univ_pi fun _ => ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet,
      volume_pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
    have h1 := mixedEmbedding.covolume_integerLattice (K := E)
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (mixedEmbedding.fundamentalDomain_integerLattice E), measureReal_def] at h1
    rw [h1]
  have hcovL : ZLattice.covolume L volume = ((2 : ℝ)⁻¹ ^ f * Real.sqrt D) ^ 2 / n := by
    have h := ReciprocityTheory.GeometryOfNumbersTheory.covol_div_covol_eq_relIndex volume L₀ L hL₀L
    have hrel : L₀.toAddSubgroup.relIndex L.toAddSubgroup = n := by
      change L₀.toAddSubgroup.relIndex (Λc.toAddSubgroup.map emb) = _
      rw [hL₀_eq, AddSubgroup.relIndex_map_map_of_injective _ _ hemb_inj]; rfl
    rw [hrel, hcovL₀] at h
    have hpos := ZLattice.covolume_pos L₀ volume
    rw [hcovL₀] at hpos
    rw [← h, div_div_cancel₀ hpos.ne']
  -- Step 4: Apply Mathlib's Minkowski Convex Body Theorem to the product of 2D Hermitian ellipsoids.
  have h2v : 2 * vInv E = D ^ ((1 : ℝ) / (2 * f)) := by
    unfold vInv fDeg
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
      zero_add]
    ring
  have hvpos : 0 < 2 * vInv E := by rw [h2v]; positivity
  set R : ℝ := Real.sqrt (2 * vInv E)
  have hR0 : 0 < R := Real.sqrt_pos.2 hvpos
  have hR2 : R ^ 2 = 2 * vInv E := Real.sq_sqrt hvpos.le
  have hpow : ((R ^ 2) ^ 2) ^ f = D := by
    have hf' : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
    rw [hR2, h2v, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hD.le,
      ← Real.rpow_mul hD.le]
    convert Real.rpow_one D using 2; field_simp; norm_num
  let S_ell : Set ({w : InfinitePlace E // w.IsComplex} → Fin 2 → ℂ) :=
    Set.univ.pi fun w => {u : Fin 2 → ℂ | (star u ⬝ᵥ (G.map w.1.embedding *ᵥ u)).re ≤ R ^ 2}
  have hvol_S : volume S_ell = ENNReal.ofReal ((Real.pi ^ 2 / 2) ^ f * D / P) := by
    change Measure.pi (fun _ => volume) S_ell = _
    rw [Measure.pi_pi]
    simp_rw [(ellipsoid_props_and_volume (hGpos _) hR0).2.2]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => by have := hdetpos w.1.embedding; positivity),
      Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      show Fintype.card {w : InfinitePlace E // w.IsComplex} = f from rfl, mul_pow, hpow]
  have hfinrk : Module.finrank ℝ ({w : InfinitePlace E // w.IsComplex} → Fin 2 → ℂ) = 4 * f := by
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex,
      show Fintype.card {w : InfinitePlace E // w.IsComplex} = f from rfl]
    ring
  let F := ZSpan.fundamentalDomain ((Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
  have hfund : IsAddFundamentalDomain L.toAddSubgroup F volume :=
    ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) volume
  have hvol_F : volume F = ENNReal.ofReal (((2 : ℝ)⁻¹ ^ f * Real.sqrt D) ^ 2 / n) := by
    have h1 := ZLattice.covolume_eq_measure_fundamentalDomain L volume hfund
    rw [hcovL, measureReal_def] at h1
    rw [← ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne, ← h1]
  have hmink : volume F * 2 ^ Module.finrank ℝ ({w : InfinitePlace E // w.IsComplex} → Fin 2 → ℂ) <
      volume S_ell := by
    rw [hvol_F, hvol_S, hfinrk,
      show (2 : ENNReal) ^ (4 * f) = ENNReal.ofReal (2 ^ (4 * f)) by norm_cast,
      ← ENNReal.ofReal_mul (by positivity)]
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
    have hs : ((2 : ℝ)⁻¹ ^ f * Real.sqrt D) ^ 2 = D / 4 ^ f := by
      rw [mul_pow, Real.sq_sqrt hD.le, ← pow_mul, mul_comm f 2, pow_mul,
        show ((2 : ℝ)⁻¹ ^ 2) = (4 : ℝ)⁻¹ by norm_num, inv_pow, div_eq_mul_inv, mul_comm]
    have h8 : (1 : ℝ) < (Real.pi ^ 2 / 8) ^ f :=
      one_lt_pow₀ (by nlinarith [Real.pi_gt_three]) hf.ne'
    have e1 : (2 : ℝ) ^ (4 * f) = 4 ^ f * 4 ^ f := by rw [← mul_pow, pow_mul]; norm_num
    have e2 : (Real.pi ^ 2 / 2) ^ f = (Real.pi ^ 2 / 8) ^ f * 4 ^ f := by rw [← mul_pow]; ring_nf
    rw [hs, e1, e2]
    calc D / 4 ^ f / n * (4 ^ f * 4 ^ f) = 4 ^ f * D / n := by field_simp
      _ ≤ 4 ^ f * D / P := div_le_div_of_nonneg_left (by positivity) hP hPn
      _ < (Real.pi ^ 2 / 8) ^ f * 4 ^ f * D / P := by
        rw [div_lt_div_iff_of_pos_right hP]; nlinarith [mul_pos (by positivity : (0 : ℝ) < 4 ^ f) hD]
  have : Countable L.toAddSubgroup :=
    (Free.chooseBasis ℤ L).repr.toEquiv.countable_iff.2 inferInstance
  obtain ⟨⟨y, hyL⟩, hy0, hyS⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hfund
    (fun y hy => Set.mem_pi.2 fun w _ =>
      (ellipsoid_props_and_volume (hGpos _) hR0).2.1 _ (Set.mem_pi.1 hy w (Set.mem_univ w)))
    (convex_pi fun w _ => (ellipsoid_props_and_volume (hGpos _) hR0).1) hmink
  -- Step 5: Pull y back to a nonzero short vector u ∈ Λ.
  obtain ⟨c, hcΛc, rfl⟩ := hyL
  let u := SemiDegIdx.combMap v c
  have hu0 : u ≠ 0 := fun h0 => hy0 <| Subtype.ext <| by
    have hc0 : c = 0 := SemiDegIdx.combMap_injective hb.2.1 (by simpa [u] using h0)
    simp [hc0]
  refine ⟨u, SemiDegIdx.mem_coordLat.1 hcΛc, hu0, fun φ => ?_⟩
  let w : {w : InfinitePlace E // w.IsComplex} := ⟨InfinitePlace.mk φ, IsTotallyComplex.isComplex _⟩
  have hre : (φ (star u ⬝ᵥ (J *ᵥ u))).re = (w.1.embedding (star u ⬝ᵥ (J *ᵥ u))).re := by
    rcases InfinitePlace.embedding_mk_eq φ with h1 | h1
    · simp [w, h1]
    · simp [w, h1, ComplexEmbedding.conjugate_coe_eq]
  have hq : (w.1.embedding (star u ⬝ᵥ (J *ᵥ u))).re =
      (star (emb c w) ⬝ᵥ (G.map w.1.embedding *ᵥ emb c w)).re := by
    congr 1; rw [← hcomb_eq c]; simp [emb, dotProduct, mulVec, map_mul, hs]
  rw [hre, hq, ← hR2]
  exact hyS w (Set.mem_univ w)

end GlobalTheory.ShortVec
