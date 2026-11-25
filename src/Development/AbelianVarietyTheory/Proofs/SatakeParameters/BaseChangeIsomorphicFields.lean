module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingEquivPlaceCorrespondencePlaceUnder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Topology Matrix
open GlobalTheory.CuspRep
open scoped ContDiff

namespace GlobalTheory.IsoPull

section Ring

variable {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] {a : ℕ}

theorem map_map_comm (p : R →+* S) (p' : R' →+* S') (c : R →+* R') (c' : S →+* S') (h : ∀ x, p' (c x) = c' (p x))
    (g : GL (Fin a) R) :
    GeneralLinearGroup.map p' (GeneralLinearGroup.map c g) =
      GeneralLinearGroup.map c' (GeneralLinearGroup.map p g) := by
  ext i j
  exact h _

theorem continuous_mapGL [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S]
    (c : R →+* S) (h : Continuous c) : Continuous (GeneralLinearGroup.map (n := Fin a) c) :=
  Continuous.units_map _ (continuous_matrix fun i j => h.comp (continuous_id.matrix_elem i j))

theorem map_unip {r : ℕ} (c : R →+* S) (x : BlockIx a r → R) :
    GeneralLinearGroup.map c (unip x) = unip fun p => c (x p) := by
  ext i j
  change c ((1 + nilM x : Matrix (Fin a) (Fin a) R) i j) =
    (1 + nilM fun p => c (x p) : Matrix (Fin a) (Fin a) S) i j
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add (f := _)]
  split_ifs <;> simp

end Ring

section Sat

open Formalism.UG GlobalTheory.LFun GlobalTheory.PRep

theorem Tj_map {F F' : Type} [Field F] [Field F'] {n : ℕ} (c : F ≃+* F') {O : Subring F} {O' : Subring F'}
    (hK : ∀ g, g ∈ GLint (Fin n) O ↔ Units.mapEquiv c.mapMatrix.toMulEquiv g ∈ GLint (Fin n) O') (ϖ : Fˣ) (j : ℕ)
    (g : GL (Fin n) F) : Tj ℂ n O' (c ϖ) j (Units.mapEquiv c.mapMatrix.toMulEquiv g) = Tj ℂ n O ϖ j g := by
  classical
  set G : GL (Fin n) F ≃* GL (Fin n) F' := Units.mapEquiv c.mapMatrix.toMulEquiv with hG
  have hGv : ∀ g i j, (G g).1 i j = c (g.1 i j) := fun _ _ _ => rfl
  have e : G (ConjPlace.dGL n ϖ j) = ConjPlace.dGL n (Units.map (c : F →* F') ϖ) j :=
    Units.ext (Matrix.ext fun a b => by
      rw [hGv]
      simp only [ConjPlace.dGL, diagJ, Matrix.diagonal_apply]
      split_ifs <;> simp)
  refine (ConjPlace.Tj_apply O' (Units.map (c : F →* F') ϖ) j _).trans ?_
  rw [ConjPlace.Tj_apply, ← e]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨a, ha, b, hb, H⟩
    obtain ⟨a, rfl⟩ := G.surjective a
    obtain ⟨b, rfl⟩ := G.surjective b
    rw [← map_mul, ← map_mul, G.apply_eq_iff_eq] at H
    exact ⟨a, (hK a).2 ha, b, (hK b).2 hb, H⟩
  · rintro ⟨a, ha, b, hb, H⟩
    exact ⟨_, (hK a).1 ha, _, (hK b).1 hb, by rw [H, map_mul, map_mul]⟩

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] {n : ℕ}
  {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem hasSatGL_of_ringEquiv (c : v.adicCompletion K ≃+* w.adicCompletion M) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (hq : qV M w = qV K v) {ρ : Representation ℂ (GL (Fin n) (v.adicCompletion K)) V}
    {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion M)) W} (T : V ≃ₗ[ℂ] W)
    (hT : ∀ g x, ρ' (GeneralLinearGroup.map c.toRingHom g) (T x) = T (ρ g x)) {B : Multiset ℂˣ}
    (h : HasSatGL v ρ B) : HasSatGL w ρ' B := by
  let G : GL (Fin n) (v.adicCompletion K) ≃* GL (Fin n) (w.adicCompletion M) := Units.mapEquiv c.mapMatrix.toMulEquiv
  have hG : ∀ g, G g = GeneralLinearGroup.map c.toRingHom g := fun g => Units.ext rfl
  have hGv : ∀ g i j, (G g).1 i j = c (g.1 i j) := fun _ _ _ => rfl
  have hO : ∀ x, c x ∈ Ov M w ↔ x ∈ Ov K v := fun x => by
    change Valued.v (c x) ≤ 1 ↔ Valued.v x ≤ 1
    rw [hc]
  have hK : ∀ g, g ∈ KGL v (n := n) ↔ G g ∈ KGL w (n := n) := fun g => by
    simp only [KGL, GlobalTheory.AdelicU.mem_GLint_iff, ← map_inv, hGv, hO]
  have hf : ∀ g y, T.toLinearMap ((ρ.comp G.symm.toMonoidHom) g y) = ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ (G.symm g) y) = ρ' g (T y)
    rw [← hT, ← hG, MulEquiv.apply_symm_apply]
  have hTj := Tj_map (n := n) c hK
  have key0 : ∀ x, IsSatVecGL v ρ x B → IsSatVecGL w (ρ.comp G.symm.toMonoidHom) x B := by
    rintro x ⟨h0, hx, hB, hH⟩
    refine ⟨h0, (mem_fixed_comp_symm _ hK).2 hx, hB, fun ϖ' hϖ' j hj => ?_⟩
    obtain ⟨p, rfl⟩ := c.surjective ϖ'
    have hp : IsUnifV K v p := (hc p).symm.trans hϖ'
    obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (v.adicCompletion K)ˣ, ϖ = p :=
      ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
    rw [heckeVec_comp_symm _ hK (Tj_mem_hecke hϖ' j).1 hx, hq, ← hH _ hp j hj]
    exact congrArg (fun t => heckeVec ρ _ t x) (funext (hTj ϖ j))
  have key : ∀ x, IsSatVecGL v ρ x B → IsSatVecGL w ρ' (T x) B := fun x hx =>
    (key0 x hx).map T.toLinearMap hf ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hG, hT] at this

end Sat

section PullCore

variable {K M : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
  [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] {a : ℕ}

structure PullData (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] (a : ℕ) where
  eRat : K →+* M
  eAd : Ad K ≃+* Ad M
  cont_eAd : Continuous eAd
  cont_eAd_symm : Continuous eAd.symm
  eAd_alg : ∀ x, eAd (algebraMap K (Ad K) x) = algebraMap M (Ad M) (eRat x)
  eAd_rat : ∀ {r : ℕ} {x : BlockIx a r → Ad K}, x ∈ ratN K a r → (fun p => eAd (x p)) ∈ ratN M a r
  eAd_symm_rat : ∀ {r : ℕ} {x : BlockIx a r → Ad M}, x ∈ ratN M a r → (fun p => eAd.symm (x p)) ∈ ratN K a r
  eInf : Cinf K →+* Cinf M
  eFin : Af K →+* Af M
  cont_eFin : Continuous eFin
  pInf_eAd : ∀ x, pInf M (eAd x) = eInf (pInf K x)
  pFin_eAd : ∀ x, pFin M (eAd x) = eFin (pFin K x)
  mapL : Lie K a →L[ℝ] Lie M a
  mapL_apply : ∀ X i j, mapL X i j = eInf (X i j)
  mapOp : Op K a → Op M a
  mapOp_fin : ∀ k, mapOp (.fin k) = .fin (GeneralLinearGroup.map eFin k)
  mapOp_cpt : ∀ k, ∃ k', mapOp (.cpt k) = .cpt k' ∧
    GeneralLinearGroup.map eInf (Unitary.toUnits k) = Unitary.toUnits k'
  mapOp_lie : ∀ X, mapOp (.lie X) = .lie (mapL X)
  height_le : ∃ C : ℝ, 1 ≤ C ∧ ∀ y : GL (Fin a) (Cinf K), height (GeneralLinearGroup.map eInf y) ≤ C * height y
  embMap : (K →+* ℂ) → (M →+* ℂ)
  eInf_atEmb : ∀ τ z, eInf (atEmb τ z) = atEmb (embMap τ) z

namespace PullData

variable (D : PullData K M a)

def mapA : GA K a →* GA M a := GeneralLinearGroup.map D.eAd.toRingHom

theorem mapA_infGL (y : GL (Fin a) (Cinf K)) :
    D.mapA (infGL K a y) = infGL M a (GeneralLinearGroup.map D.eInf y) :=
  ga_ext (by rw [mapA, map_map_comm _ _ _ _ D.pInf_eAd, pInf_infGL, pInf_infGL])
    (by rw [mapA, map_map_comm _ _ _ _ D.pFin_eAd, pFin_infGL, pFin_infGL, map_one])

theorem mapA_finGL (k : GL (Fin a) (Af K)) :
    D.mapA (finGL K a k) = finGL M a (GeneralLinearGroup.map D.eFin k) :=
  ga_ext (by rw [mapA, map_map_comm _ _ _ _ D.pInf_eAd, pInf_finGL, pInf_finGL, map_one])
    (by rw [mapA, map_map_comm _ _ _ _ D.pFin_eAd, pFin_finGL, pFin_finGL])

theorem mapA_ratGL (γ : GL (Fin a) K) :
    D.mapA (ratGL K a γ) = ratGL M a (GeneralLinearGroup.map D.eRat γ) :=
  Units.ext (Matrix.ext fun _ _ => D.eAd_alg _)

theorem chart_map (φ : GA M a → ℂ) (g : GA K a) {x : Lie K a} (hx : x ∈ invSet K a) :
    chart (fun g => φ (D.mapA g)) g x = chart φ (D.mapA g) (D.mapL x) ∧ D.mapL x ∈ invSet M a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  have hm : D.mapL (toL u.val) = toL (GeneralLinearGroup.map D.eInf u).val :=
    funext₂ fun i j => D.mapL_apply _ i j
  rw [hm, chart_val, chart_val, map_mul, D.mapA_infGL]
  exact ⟨rfl, val_mem_invSet _⟩

theorem map_mem_Sm {φ : GA M a → ℂ} (hφ : φ ∈ Sm M a) : (fun g => φ (D.mapA g)) ∈ Sm K a := fun g =>
  ((hφ (D.mapA g)).comp D.mapL.contDiff.contDiffOn
    fun _ hx => (D.chart_map φ g hx).2).congr fun _ hx => (D.chart_map φ g hx).1

def pull (hinv : ∀ {φ : GA K a → ℂ}, φ ∈ Sm K a →
    (fun g => φ (GeneralLinearGroup.map D.eAd.symm.toRingHom g)) ∈ Sm M a) : Sm M a ≃ₗ[ℂ] Sm K a where
  toFun φ := ⟨fun g => φ.1 (D.mapA g), D.map_mem_Sm φ.2⟩
  invFun φ := ⟨fun g => φ.1 (GeneralLinearGroup.map D.eAd.symm.toRingHom g), hinv φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| funext fun _ => congrArg φ.1 (Units.ext (Matrix.ext fun _ _ => D.eAd.apply_symm_apply _))
  right_inv φ := Subtype.ext <| funext fun _ => congrArg φ.1 (Units.ext (Matrix.ext fun _ _ => D.eAd.symm_apply_apply _))

variable {D}

theorem rt_pull {hinv} (h : GA K a) (φ : Sm M a) :
    rt K a h (D.pull hinv φ) = D.pull hinv (rt M a (D.mapA h) φ) :=
  Subtype.ext <| funext fun g => congrArg φ.1 (map_mul D.mapA g h)

theorem lie_pull {hinv} (X : Lie K a) (φ : Sm M a) :
    lie K a X (D.pull hinv φ) = D.pull hinv (lie M a (D.mapL X) φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have e1 : chart (D.pull hinv φ).1 g =ᶠ[𝓝 (oneL K a)] chart φ.1 (D.mapA g) ∘ D.mapL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (D.chart_map φ.1 g hx).1
  have h1 : D.mapL (oneL K a) = oneL M a := by
    funext i j
    rw [D.mapL_apply]
    change D.eInf ((1 : Matrix (Fin a) (Fin a) (Cinf K)) i j) = (1 : Matrix (Fin a) (Fin a) (Cinf M)) i j
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h2 := HasFDerivAt.comp (oneL K a) (f := D.mapL)
    (by rw [h1]; exact (differentiableAt_chart φ.2 (D.mapA g)).hasFDerivAt) D.mapL.hasFDerivAt
  change fderiv ℝ _ _ X = fderiv ℝ _ _ _
  rw [e1.fderiv_eq, h2.fderiv]
  rfl

theorem act_pull {hinv} (o : Op K a) (φ : Sm M a) :
    act o (D.pull hinv φ) = D.pull hinv (act (D.mapOp o) φ) := by
  cases o with
  | fin k => rw [D.mapOp_fin]; exact (D.rt_pull _ φ).trans (by rw [D.mapA_finGL]; rfl)
  | cpt k =>
    obtain ⟨k', hk1, hk2⟩ := D.mapOp_cpt k
    rw [hk1]
    exact (D.rt_pull (infGL K a (Unitary.toUnits k)) φ).trans (by rw [D.mapA_infGL, hk2]; rfl)
  | lie X => rw [D.mapOp_lie]; exact D.lie_pull X φ

theorem Eop_pull {hinv} (τ : K →+* ℂ) (i j : Fin a) (φ : Sm M a) :
    Eop τ i j (D.pull hinv φ) = D.pull hinv (Eop (D.embMap τ) i j φ) := by
  have h2 : ∀ z, lieS K a i j (atEmb τ z) (D.pull hinv φ) =
      D.pull hinv (lieS M a i j (atEmb (D.embMap τ) z) φ) := fun z => by
    have e' : ∀ x, D.mapL (toL (Matrix.single i j x)) = toL (Matrix.single i j (D.eInf x)) := fun x => by
      funext k l
      rw [D.mapL_apply]
      change D.eInf (Matrix.single i j x k l) = Matrix.single i j (D.eInf x) k l
      rw [Matrix.single_apply, Matrix.single_apply]
      split_ifs <;> simp
    rw [lieS_apply, D.lie_pull, e', D.eInf_atEmb, lieS_apply]
  have hsub (x y : Sm M a) : D.pull hinv (x - y) = D.pull hinv x - D.pull hinv y :=
    (D.pull hinv).toLinearMap.map_sub x y
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, h2, (D.pull hinv).map_smul, hsub]

theorem cap_pull {hinv} (σ : K →+* ℂ) (u : ℂ) (φ : Sm M a) :
    cap σ u (D.pull hinv φ) = D.pull hinv (cap (D.embMap σ) u φ) := by
  have h := map_qdet ((D.pull hinv).conjAlgEquiv ℂ).toAlgHom (Eop (D.embMap σ)) (u + ((a : ℂ) - 1) / 2)
  have e1 : (fun i j => ((D.pull hinv).conjAlgEquiv ℂ).toAlgHom (Eop (D.embMap σ) i j)) = Eop σ := by
    funext i j
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := (D.pull hinv).surjective ψ
    rw [D.Eop_pull]
    change D.pull hinv (Eop (D.embMap σ) i j ((D.pull hinv).symm (D.pull hinv ψ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [e1] at h
  rw [cap, ← h, cap]
  generalize Formalism.REAL.qdet (Eop (a := a) (D.embMap σ)) (u + ((a : ℂ) - 1) / 2) = z
  change D.pull hinv (z ((D.pull hinv).symm (D.pull hinv φ))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem Zalg_pull {hinv} {z : Module.End ℂ (Sm K a)} (hz : z ∈ Zalg K a) :
    ∃ z' ∈ Zalg M a, ∀ φ, z (D.pull hinv φ) = D.pull hinv (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨_, Algebra.subset_adjoin ⟨_, _, rfl⟩, D.cap_pull τ u⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩

theorem isAutForm_pull {hinv} {φ : Sm M a} (h : IsAutForm φ) : IsAutForm (D.pull hinv φ) := by
  refine { left := ?_, level := ?_, kfin := ?_, zfin := ?_, growth := ?_ }
  · intro γ g
    change φ.1 (D.mapA (ratGL K a γ * g)) = φ.1 (D.mapA g)
    rw [map_mul, D.mapA_ratGL, h.left]
  · convert h.level.preimage (continuous_mapGL D.eFin D.cont_eFin) using 1
    ext k
    have hact := D.act_pull (hinv := hinv) (.fin k) φ
    rw [D.mapOp_fin] at hact
    exact (Eq.congr_left hact).trans (D.pull hinv).injective.eq_iff
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep M a k φ)).map
      (D.pull hinv).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    obtain ⟨k', hk1, -⟩ := D.mapOp_cpt k
    exact ⟨_, Submodule.subset_span ⟨k', rfl⟩, (hk1 ▸ D.act_pull (.cpt k) φ).symm⟩
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm M a) => z φ) ''
      Zalg M a)).map (D.pull hinv).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := D.Zalg_pull hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  · intro g
    obtain ⟨C, N, h1⟩ := h.growth (D.mapA g)
    obtain ⟨K₀, hK1, hK⟩ := D.height_le
    refine ⟨C * K₀ ^ N, N, fun y => ?_⟩
    change ‖φ.1 (D.mapA (g * infGL K a y))‖ ≤ _
    rw [map_mul, D.mapA_infGL]
    have h1ge : ∀ {F : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F]
        (z : GL (Fin a) (Cinf F)), 1 ≤ height z := fun z => by
      unfold height; linarith [norm_nonneg (toL z.val), norm_nonneg (toL (z⁻¹).val)]
    have hy := h1 (GeneralLinearGroup.map D.eInf y)
    have hC : 0 ≤ C := by
      by_contra hc
      have hpos : 0 < height (GeneralLinearGroup.map D.eInf y) ^ N :=
        pow_pos (lt_of_lt_of_le one_pos (h1ge _)) N
      linarith [mul_neg_of_neg_of_pos (lt_of_not_ge hc) hpos,
        norm_nonneg (φ.1 (D.mapA g * infGL M a (GeneralLinearGroup.map D.eInf y)))]
    refine hy.trans ?_
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_trans zero_le_one (h1ge _)) (hK y) N) hC

open MeasureTheory in
theorem isCuspidal_pull (D : PullData K M a) {φ : GA M a → ℂ} (hφ : IsCuspidal φ) :
    IsCuspidal fun g => φ (D.mapA g) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  borelize (BlockIx a r → Ad M)
  let β : (BlockIx a r → Ad K) ≃ₜ+ (BlockIx a r → Ad M) :=
    { toFun := fun x p => D.eAd (x p)
      invFun := fun x p => D.eAd.symm (x p)
      left_inv := fun x => funext fun p => D.eAd.symm_apply_apply _
      right_inv := fun x => funext fun p => D.eAd.apply_symm_apply _
      map_add' := fun x y => funext fun p => map_add D.eAd _ _
      continuous_toFun := continuous_pi fun p => D.cont_eAd.comp (continuous_apply p)
      continuous_invFun := continuous_pi fun p => D.cont_eAd_symm.comp (continuous_apply p) }
  let q : ratN M a r ≃ ratN K a r :=
    { toFun := fun y => ⟨β.symm y, D.eAd_symm_rat y.2⟩
      invFun := fun x => ⟨β x, D.eAd_rat x.2⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hφ r h0 h1 (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving q fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add (f := _), β.apply_symm_apply]) (D.mapA g)
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  beta_reduce
  rw [map_mul, mapA, map_unip]
  rfl

def pullSub (D : PullData K M a) {hinv}
    (hpull_act : ∀ (o : Op M a), ∃ o' : Op K a, ∀ φ, D.pull hinv (act o φ) = act o' (D.pull hinv φ))
    (π : CuspSub M a) : CuspSub K a where
  V := π.V.map (D.pull hinv).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact ⟨D.isAutForm_pull (π.cusp φ hφ).1, D.isCuspidal_pull (π.cusp φ hφ).2⟩
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable _ φ hφ, (D.act_pull o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := D.pull hinv)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (D.pull hinv).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (D.pull hinv).injective h2]) fun o φ hφ => by
      change D.pull hinv (act o φ) ∈ W
      obtain ⟨o', ho'⟩ := hpull_act o
      rw [ho']
      exact hs o' _ hφ
    have e1 := Submodule.map_comap_eq_of_surjective (f := (D.pull hinv).toLinearMap) (D.pull hinv).surjective W
    exact h.imp (fun h => by rw [← e1, h, Submodule.map_bot]) fun h => by rw [← e1, h]

end PullData

end PullCore

variable {K M : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M]
  {a : ℕ} (e : K ≃+* M)

def mapL : Lie K a →L[ℝ] Lie M a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => cInf e (X i j)
      map_add' := fun X Y => by funext i j; simp
      map_smul' := fun t X => by funext i j; exact cInf_smul e t _ }

def mapK (k : Kinf K a) : Kinf M a :=
  ⟨k.1.map (cInf e), Matrix.mem_unitaryGroup_iff.2 (by
    have h : star (k.1.map (cInf e)) = (star k.1).map (cInf e) := by
      ext i j : 1
      exact (cInf_star e _).symm
    rw [h, ← Matrix.map_mul, Matrix.mem_unitaryGroup_iff.1 k.2]
    exact Matrix.map_one _ (map_zero _) (map_one _))⟩

def mapOp : Op K a → Op M a
  | .fin k => .fin (GeneralLinearGroup.map (cFin e) k)
  | .cpt k => .cpt (mapK e k)
  | .lie X => .lie (mapL e X)

theorem mapOp_symm (o : Op K a) : mapOp e.symm (mapOp e o) = o := by
  cases o with
  | fin k => exact congrArg Op.fin (Units.ext (Matrix.ext fun i j => cFin_symm e _))
  | cpt k => exact congrArg Op.cpt (Subtype.ext (Matrix.ext fun i j => cInf_symm e _))
  | lie X => exact congrArg Op.lie (funext₂ fun i j => cInf_symm e _)

omit [_root_.NumberField.IsTotallyComplex K] [_root_.NumberField.IsTotallyComplex M] in
theorem height_map_le (y : GL (Fin a) (Cinf K)) : height (GeneralLinearGroup.map (cInf e) y) ≤ height y := by
  have h1 : ∀ y : GL (Fin a) (Cinf K), ‖toL (GeneralLinearGroup.map (cInf e) y).val‖ ≤ ‖toL y.val‖ := fun y =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j =>
      (norm_cInf_le e _).trans ((norm_le_pi_norm (toL y.val i) j).trans (norm_le_pi_norm (toL y.val) i))
  unfold height
  rw [← map_inv]
  linarith [h1 y, h1 y⁻¹]

theorem height_map (y : GL (Fin a) (Cinf K)) : height (GeneralLinearGroup.map (cInf e) y) = height y := by
  refine le_antisymm (height_map_le e y) (le_of_eq_of_le ?_ (height_map_le e.symm _))
  exact congrArg height (Units.ext (Matrix.ext fun i j => (cInf_symm e _).symm))

theorem map_mem_ratN {r : ℕ} {x : BlockIx a r → Ad K} (hx : x ∈ ratN K a r) :
    (fun p => cAd e (x p)) ∈ ratN M a r := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨fun p => e (y p), funext fun p => (cAd_algebraMap e (y p)).symm⟩

def isoData (a : ℕ) : PullData K M a where
  eRat := e.toRingHom
  eAd :=
    { toFun := cAd e
      invFun := cAd e.symm
      left_inv := cAd_symm e
      right_inv := cAd_symm e.symm
      map_mul' := map_mul (cAd e)
      map_add' := map_add (cAd e) }
  cont_eAd := continuous_cAd e
  cont_eAd_symm := continuous_cAd e.symm
  eAd_alg := cAd_algebraMap e
  eAd_rat := map_mem_ratN e
  eAd_symm_rat := map_mem_ratN e.symm
  eInf := cInf e
  eFin := cFin e
  cont_eFin := continuous_cFin e
  pInf_eAd := pInf_cAd e
  pFin_eAd := pFin_cAd e
  mapL := mapL e
  mapL_apply _ _ _ := rfl
  mapOp := mapOp e
  mapOp_fin _ := rfl
  mapOp_cpt k := ⟨mapK e k, rfl, Units.ext rfl⟩
  mapOp_lie _ := rfl
  height_le := ⟨1, le_rfl, fun y => by rw [one_mul, height_map e]⟩
  embMap σ := σ.comp e.symm.toRingHom
  eInf_atEmb σ z := by
    have h : (σ.comp e.symm.toRingHom).comp e.toRingHom = σ := by ext x; simp
    simpa only [h] using cInf_atEmb e (σ.comp e.symm.toRingHom) z

variable (a) in
def mapA : GA K a →* GA M a := GeneralLinearGroup.map (cAd e)

theorem mapA_symm (g : GA K a) : mapA a e.symm (mapA a e g) = g := by
  ext i j : 2
  exact cAd_symm e _

theorem mapA_infGL (y : GL (Fin a) (Cinf K)) :
    mapA a e (infGL K a y) = infGL M a (GeneralLinearGroup.map (cInf e) y) :=
  (isoData e a).mapA_infGL y

theorem mapA_finGL (k : GL (Fin a) (Af K)) : mapA a e (finGL K a k) = finGL M a (GeneralLinearGroup.map (cFin e) k) :=
  (isoData e a).mapA_finGL k

theorem mapA_ratGL (γ : GL (Fin a) K) :
    mapA a e (ratGL K a γ) = ratGL M a (GeneralLinearGroup.map e.toRingHom γ) :=
  (isoData e a).mapA_ratGL γ

theorem chart_map (φ : GA M a → ℂ) (g : GA K a) {x : Lie K a} (hx : x ∈ invSet K a) :
    chart (fun g => φ (mapA a e g)) g x = chart φ (mapA a e g) (mapL e x) ∧ mapL e x ∈ invSet M a :=
  (isoData e a).chart_map φ g hx

theorem map_mem_Sm {φ : GA M a → ℂ} (hφ : φ ∈ Sm M a) : (fun g => φ (mapA a e g)) ∈ Sm K a :=
  (isoData e a).map_mem_Sm hφ

variable (a) in
def pull : Sm M a ≃ₗ[ℂ] Sm K a := (isoData e a).pull (map_mem_Sm e.symm)

theorem pull_apply (φ : Sm M a) (g : GA K a) : (pull a e φ).1 g = φ.1 (mapA a e g) := rfl

theorem rt_pull (h : GA K a) (φ : Sm M a) : rt K a h (pull a e φ) = pull a e (rt M a (mapA a e h) φ) :=
  (isoData e a).rt_pull h φ

theorem lie_pull (X : Lie K a) (φ : Sm M a) : lie K a X (pull a e φ) = pull a e (lie M a (mapL e X) φ) :=
  (isoData e a).lie_pull X φ

theorem act_pull (o : Op K a) (φ : Sm M a) : act o (pull a e φ) = pull a e (act (mapOp e o) φ) :=
  (isoData e a).act_pull o φ

theorem pull_act (o : Op M a) (φ : Sm M a) : pull a e (act o φ) = act (mapOp e.symm o) (pull a e φ) := by
  rw [act_pull]
  exact congrArg (fun o => pull a e (act o φ)) (mapOp_symm e.symm o).symm

theorem Eop_pull (τ : M →+* ℂ) (i j : Fin a) (φ : Sm M a) :
    Eop (τ.comp e.toRingHom) i j (pull a e φ) = pull a e (Eop τ i j φ) := by
  have h := (isoData e a).Eop_pull (hinv := map_mem_Sm e.symm) (τ.comp e.toRingHom) i j φ
  change Eop (τ.comp e.toRingHom) i j (pull a e φ) =
    pull a e (Eop ((τ.comp e.toRingHom).comp e.symm.toRingHom) i j φ) at h
  rwa [show (τ.comp e.toRingHom).comp e.symm.toRingHom = τ from by ext x; simp] at h

theorem cap_pull' (σ : K →+* ℂ) (u : ℂ) (φ : Sm M a) :
    cap σ u (pull a e φ) = pull a e (cap (σ.comp e.symm.toRingHom) u φ) :=
  (isoData e a).cap_pull σ u φ

theorem cap_pull (τ : M →+* ℂ) (u : ℂ) (φ : Sm M a) :
    cap (τ.comp e.toRingHom) u (pull a e φ) = pull a e (cap τ u φ) := by
  simpa only [show (τ.comp e.toRingHom).comp e.symm.toRingHom = τ from by ext x; simp] using
    cap_pull' e (τ.comp e.toRingHom) u φ

theorem Zalg_pull {z : Module.End ℂ (Sm K a)} (hz : z ∈ Zalg K a) :
    ∃ z' ∈ Zalg M a, ∀ φ, z (pull a e φ) = pull a e (z' φ) :=
  (isoData e a).Zalg_pull hz

theorem isAutForm_pull {φ : Sm M a} (h : IsAutForm φ) : IsAutForm (pull a e φ) :=
  (isoData e a).isAutForm_pull h

theorem isCuspidal_pull {φ : GA M a → ℂ} (hφ : IsCuspidal φ) : IsCuspidal fun g => φ (mapA a e g) :=
  (isoData e a).isCuspidal_pull hφ

def pullSub (π : CuspSub M a) : CuspSub K a :=
  (isoData e a).pullSub (fun o => ⟨mapOp e.symm o, pull_act e o⟩) π

theorem hasInfChar_pullSub {π : CuspSub M a} {σ : K →+* ℂ} {m : Multiset ℂ}
    (h : π.HasInfChar (σ.comp e.symm.toRingHom) m) : (pullSub e π).HasInfChar σ m := by
  refine ⟨h.1, ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap σ u (pull a e φ) = _ • pull a e φ
  rw [cap_pull', h.2 u φ hφ, map_smul]

theorem hasSat_pullSub {π : CuspSub M a} {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (hw : Over e v w) {B : Multiset ℂˣ} (h : (CG.mk π).HasSat w B) : (CG.mk (pullSub e π)).HasSat v B := by
  rw [CG.hasSat_mk] at h ⊢
  refine hasSatGL_of_ringEquiv (locEquiv hw.symm) (valued_cLoc hw.symm) (qV_eq hw.symm)
    ((pull a e).submoduleMap π.V) (fun g x => Subtype.ext ?_) h
  refine Eq.trans ?_ (pull_act e (.fin (locGL M a w g)) x.1).symm
  change _ = act (.fin (GeneralLinearGroup.map (cFin e.symm) (locGL M a w g))) (pull a e x.1)
  rw [cFin_locGL hw.symm]
  rfl

end GlobalTheory.IsoPull

end
