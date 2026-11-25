module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteRationalPointsCompletedLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDetSmulSubOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutProdA
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutLatA
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutTraceA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPoincareSeriesThetaVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCMRealLineAddNoPhase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLatticeSelfDualFgFullIndex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexMapNsmulComapEqAbsNormDet
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldPoincareSeriesLatticeFourier
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutLat
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutSerA
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.FinIdemSmulOfReal
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.QInertHolds
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SpanInfRatF
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionInvariantRationalTarget

/-! # RedWpAutLat: Consolidated global theta-kernel definitions and proofs (RedWpAutLat). -/
@[expose] public section

open scoped Classical ComplexOrder Kronecker Topology
open GlobalTheory.FinLatF GlobalTheory.FinWeil GlobalTheory.LFun GlobalTheory.WeilM GlobalTheory.WeilPartsF
open PositivityTheory.ThKW (Ctx_k)
open UpperTheory.TP.W (GoodK IsLatRepL)

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
  MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealWeilF
open AddChar (map_add_eq_mul)
open Complex (exp)
open Real (pi)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section
open scoped BoundedContinuousFunction ContDiff
open GlobalTheory.RealWeil Classical PositivityTheory.ThKW.RealC
open UpperTheory.TP.W (GoodK)
theorem PositivityTheory.ThKW.hermitian_form_selfadjoint_global : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E),
      GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧
        (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ
  have hτ := hB.cm.2.2.2
  constructor
  · unfold HMF
    rw [blk_conjTranspose]
    congr 1 <;> funext w
    · rw [conjTranspose_smul, herm_map (hτ _) hT]
      simp
    · rw [conjTranspose_nonsing_inv, herm_map (hτ _) hS]
  · have h0 : ∀ w : InfinitePlace F, ((2 * ((B.emb w).1 ξ₀).im : ℝ) : ℂ) ≠ 0 := fun w =>
      Complex.ofReal_ne_zero.2 (mul_ne_zero two_ne_zero (im_xi (hτ _) hξ hσ))
    have : HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *
        blk (fun w => ((2 * ((B.emb w).1 ξ₀).im : ℝ) : ℂ)⁻¹ • (JT.map (B.emb w).1)⁻¹)
          (fun w => JS.map (B.emb w).1) = 1 := by
      unfold HMF
      rw [blk_mul, ← blk_one]
      congr 1 <;> funext w
      · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (h0 w), one_smul,
          mul_nonsing_inv _ (unit_map _ hT)]
      · rw [mul_nonsing_inv _ (unit_map _ hS)]
    exact (isUnit_det_of_right_inverse this).ne_zero
end

noncomputable section
namespace PositivityTheory.ThKW
namespace AutLatA
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT)
  E} {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E} {Λ : Submodule (𝓞
  E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ} {Om : GAF σ JS × GAF σ
  JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
theorem mem_iff_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ)) (y : Matrix (Fin nT) (Fin nS) E) :
    finRatF F y ∈ latF F E nS nT Λ ↔ y ∈ Λ :=
  ⟨fun h => (hR y).2 fun M' hM' => (PositivityTheory.ThKW.gamQF_eq_one_iff'_k C y M').1 ((hA _).1 h _
    (finRatF_mem_of hM')),
    finRatF_mem_of⟩
theorem sdQ_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hR : RatSD σ JS JT ξ₀ Λ) : SelfDual (gamQF σ JS
  JT ξ₀ B.ψ) Λ := fun x =>
  (hR x).trans (forall₂_congr fun y _ => (PositivityTheory.ThKW.gamQF_eq_one_iff'_k C x y).symm)
theorem norm_emb_eq_k (hB : GoodK σ B) (φ : E →+* ℂ) (x : E) :
    ∃ v : InfinitePlace F, ‖φ x‖ = ‖tauB B v x‖ := by
  have hcm := hB.cm
  let ρ : F →+* ℂ := φ.comp (algebraMap F E)
  refine ⟨InfinitePlace.mk ρ, ?_⟩
  have hρ : ComplexEmbedding.IsReal ρ := by
    have := hcm.1.isReal (InfinitePlace.mk ρ)
    rwa [InfinitePlace.isReal_mk_iff] at this
  have he : (InfinitePlace.mk ρ).embedding = ρ := by
    rcases InfinitePlace.embedding_mk_eq ρ with h | h
    · exact h
    · rw [h]; exact hρ
  have hτ := (B.emb (InfinitePlace.mk ρ)).2.trans he
  obtain ⟨c, hc⟩ := PI.OmLocU.Red.fix_range σ hcm (y := x * σ x) (by
    rw [map_mul, PositivityTheory.ThKW.LatA.sig_sig_k hB, mul_comm])
  have key : ∀ τ : E →+* ℂ, τ.comp (algebraMap F E) = ρ → Complex.normSq (τ x) = ρ c := fun τ hτ => by
    rw [← hτ, RingHom.comp_apply, hc, map_mul, hcm.2.2.2 τ]
    exact (Complex.mul_conj (τ x)).symm
  have h2 := (key φ rfl).trans (key _ hτ).symm
  rw [Complex.ofReal_inj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
theorem finLat_k (hB : GoodK σ B) (hG : GoodLat Λ) (R : ℝ) : {y | y ∈ Λ ∧
  ‖infRatF (tauB B) y‖ ≤ R}.Finite := by
  obtain ⟨d, hd, hdi⟩ := exists_denomM hG.fg
  have hS := GlobalTheory.CompletedLatticeFinite.finite_of_denom d hd R
  refine (Set.Finite.pi fun _ : Fin nT => Set.Finite.pi fun _ : Fin nS => hS).subset ?_
  rintro y ⟨hy, hR⟩ i - j -
  refine ⟨hdi y hy i j, fun φ => ?_⟩
  obtain ⟨v, hv⟩ := norm_emb_eq_k hB φ (y i j)
  rw [hv]
  exact (norm_le_pi_norm (infRatF (tauB B) y) ((i, j), v)).trans hR
theorem isHeisQ_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hc : HeisClosedF σ JS JT ξ₀ B.ψ) (hw : w +
  sgOF σ w = 1) :
    IsHeis (sgOF σ) w (gamQF σ JS JT ξ₀ B.ψ) fun x => opFF hc w (finRatF F x) := by
  have H := isHeis_opFF (PositivityTheory.ThKW.LatA.sig_sig_k C.good) C.hS C.hT C.hξ hc hw
  have e : ∀ x y, gamQF σ JS JT ξ₀ B.ψ x y = gamFF σ JS JT ξ₀ B.ψ (finRatF F x) (finRatF F y) := fun _ _ => rfl
  exact ⟨H.sg_sg, H.w_add, fun x y z => by rw [e, e, e, map_add (f := _), H.add_left],
    fun x y z => by rw [e, e, e, map_add (f := _), H.add_right], fun x => by rw [e, H.alt],
    fun r x y => by rw [e, e, map_smul, map_smul, H.adj], fun v => by rw [map_zero, H.zero],
    fun x y v => by rw [H.comp, e, map_smul, map_add (f := _)]⟩
theorem idx_eq_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) =
      Λ.toAddSubgroup.relIndex (Λ.toAddSubgroup.comap (GlobalTheory.RatAut.sandw b a).toAddMonoidHom) := by
  have hmem := mem_iff_k C hR hO.sd
  have hfin := hO.fin (g⁻¹, h⁻¹)
  have hmov : ∀ u ∈ latF F E nS nT Λ,
      idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • u ∈
        (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)) := fun u hu => by
    rw [mem_map_rho, map_nsmul]
    exact AddSubgroup.nsmul_relIndex_mem (latF F E nS nT Λ).toAddSubgroup (Submodule.mem_map_of_mem hu)
  rw [GlobalTheory.FinWeil.idx, ← GlobalTheory.RatLattice.relIndex_comap_comap (finRatF F (E := E) (nS := nS) (nT :=
    nT)).toAddMonoidHom]
  · congr 1
    · ext x; exact hmem x
    · ext x
      show finRatF F x ∈ (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)) ↔ b * x * a ∈ Λ
      rw [mem_map_rho, _root_.PositivityTheory.ThKW.TauSpanIdentities.rhoFF_finRatF ha hb, hmem]
  · intro z hz
    have hN := Nat.pos_of_ne_zero hfin
    obtain ⟨γ, hγ⟩ := lat_approx hG _ (incAF F E ((idx (latF F E nS nT Λ)
      ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) : ℕ) : E)⁻¹ • z).fin
    obtain ⟨u, hu, e⟩ : ∃ u ∈ latF F E nS nT Λ, z = finRatF F (idx (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • γ) +
        idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • u :=
      ⟨_, hγ, by rw [map_nsmul, ← nsmul_add, add_sub_cancel, _root_.PositivityTheory.ThKW.LatC.nsmul_inv_smul (F := F) (E := E) hN]⟩
    refine ⟨idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g⁻¹, h⁻¹))) • γ, ?_, ?_⟩
    · show finRatF F _ ∈ (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))
      rw [eq_sub_of_add_eq e.symm]
      exact sub_mem hz (hmov u hu)
    · show z - finRatF F _ ∈ latF F E nS nT Λ
      rw [sub_eq_of_eq_add' e]
      exact nsmul_mem hu _
open GlobalTheory.RatAut in
theorem data_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x) ∧
    ∃ (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (c N M : ℕ), n ≠ 0 ∧ c ≠ 0 ∧ N ≠ 0 ∧
      (∀ k, b * t k * a - t k ∈ Λ) ∧ (∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) ∧
      ∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k) = lam n ∧ lam n ^ 2 = n ∧
      ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ - 1).det)| ∧
      ((c * idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) : ℕ) : ℚ) =
        |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ).det)| := by
  have sd := sdQ_k C hR
  obtain ⟨d, hd0, hdi⟩ := exists_denomM hG.fg
  have fg : Λ.toAddSubgroup.FG := GlobalTheory.RatLattice.fg_of_denom _ d hd0 hdi
  have full := hG.den
  rw [idx_eq_k C hG hR hO ha hb]
  rw [← det_sandw] at hΔ ⊢
  rw [← det_sandw_sub_one] at hd ⊢
  have hbij : Function.Bijective ⇑(sandw b a - 1) :=
    (Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 hd.isUnit)
  refine ⟨hbij, ?_⟩
  set A := Λ.toAddSubgroup with hA
  obtain ⟨N, hN, hNA⟩ : ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ A, N • sandw b a x ∈ A := by
    obtain ⟨s, hs⟩ := fg
    choose k hk hk' using full
    refine ⟨∏ y ∈ s, k (sandw b a y), Finset.prod_ne_zero_iff.2 fun y _ => (hk _).ne', fun x hx => ?_⟩
    suffices h : ∀ z : A, (∏ y ∈ s, k (sandw b a y)) • sandw b a z.1 ∈ A by
      exact h ⟨x, hx⟩
    intro z
    have hz : z ∈ AddSubsemigroup.closure (s : Set A) := by rw [hs]; trivial
    induction hz using AddSubsemigroup.closure_induction with
    | mem z hz =>
      obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun y : A => k (sandw b a y)) (show z ∈ s from hz)
      rw [hm, mul_comm, mul_smul]
      exact nsmul_mem (hk' _) m
    | add x y _ _ hx hy =>
      change (∏ y ∈ s, k (sandw b a y)) • sandw b a (x.1 + y.1) ∈ A
      rw [map_add, smul_add]
      exact add_mem hx hy
  have i1 := _root_.GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det _ _ A fg full (sandw b a - 1) N hN hd fun x
    hx => by
    rw [LinearMap.sub_apply, smul_sub]
    exact sub_mem (hNA x hx) (nsmul_mem hx N)
  have i2 := _root_.GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det _ _ A fg full (sandw b a) N hN hΔ hNA
  set B₁ := A.comap (sandw b a - 1).toAddMonoidHom with hB₁
  set B₂ := A.comap (sandw b a).toAddMonoidHom with hB₂
  set NA := A.map (N • AddMonoidHom.id _) with hNA'
  have e12 : A ⊓ B₁ = A ⊓ B₂ := by
    ext x
    refine and_congr_right fun hx => ?_
    show sandw b a x - x ∈ A ↔ sandw b a x ∈ A
    exact ⟨fun h => by simpa using add_mem h hx, fun h => sub_mem h hx⟩
  have hle : NA ≤ A ⊓ B₂ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨nsmul_mem hx N, ?_⟩
    show sandw b a (N • x) ∈ A
    rw [map_nsmul]
    exact hNA x hx
  have m1 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₁) B₁ (e12 ▸ hle) inf_le_right
  have m2 := AddSubgroup.relIndex_mul_relIndex NA (A ⊓ B₂) B₂ hle inf_le_right
  rw [AddSubgroup.inf_relIndex_right] at m1 m2
  rw [e12] at m1
  have h0 : NA.relIndex (A ⊓ B₂) * A.relIndex B₁ ≠ 0 := by
    rw [m1, ← Nat.cast_ne_zero (R := ℚ), i1, abs_ne_zero, Algebra.norm_ne_zero_iff]
    exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hN)) hd
  obtain ⟨t, t1, t2⟩ := exists_transversal A B₁ (right_ne_zero_of_mul h0)
  obtain ⟨g1, g2⟩ := gauss_isometry (isHeisQ_k C hc hO.hw) hO.good sd ((sandw b
    a).restrictScalars (𝓞 E))
    (fun x y => by
      show gamFF σ JS JT ξ₀ B.ψ (finRatF F (b * x * a)) (finRatF F (b * y * a)) =
        gamFF σ JS JT ξ₀ B.ψ (finRatF F x) (finRatF F y)
      rw [← _root_.PositivityTheory.ThKW.TauSpanIdentities.rhoFF_finRatF ha hb, ← _root_.PositivityTheory.ThKW.TauSpanIdentities.rhoFF_finRatF ha hb]
      unfold gamFF
      rw [coe_rhoFF, coe_rhoFF, PositivityTheory.ThKW.symplOF_actOF_k C]) hbij.2 _ t t1 t2
  exact ⟨_, t, _, N, _, right_ne_zero_of_mul h0, left_ne_zero_of_mul h0, hN, t1, t2, g1, g2, m1 ▸ i1, m2 ▸ i2⟩
end AutLatA
end PositivityTheory.ThKW
end

noncomputable section
namespace PositivityTheory.ThKW
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT)
  E} {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E} {Λ : Submodule (𝓞
  E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ} {Om : GAF σ JS × GAF σ
  JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)} {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
theorem finRatF_mem_iff_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT
  ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ)) (y : Matrix (Fin nT) (Fin nS) E) :
    finRatF F y ∈ latF F E nS nT Λ ↔ y ∈ Λ := AutLatA.mem_iff_k C hR hA y
theorem finite_lat_k (hB : GoodK σ B) (hG : GoodLat Λ) (R : ℝ) : {y | y ∈ Λ ∧
  ‖infRatF (tauB B) y‖ ≤ R}.Finite :=
  AutLatA.finLat_k hB hG R
theorem finite_data_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀
  Λ)
    (hO : IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x) ∧
    ∃ (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (c N M : ℕ), n ≠ 0 ∧ c ≠ 0 ∧ N ≠ 0 ∧
      (∀ k, b * t k * a - t k ∈ Λ) ∧ (∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) ∧
      ∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k) = lam n ∧ lam n ^ 2 = n ∧
      ((c * n : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ - 1).det)| ∧
      ((c * idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) : ℕ) : ℚ) =
        |Algebra.norm ℚ ((N : E) ^ M * (b ⊗ₖ aᵀ).det)| :=
  AutLatA.data_k C hG hR hO ha hb hΔ hd
end PositivityTheory.ThKW
end

noncomputable section
namespace PositivityTheory.ThKW
open scoped Topology Kronecker ComplexOrder Classical ContDiff
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.WeilPartsF
  PositivityTheory.ThKW.Trc PositivityTheory.ThKW.SerA
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT)
  E} {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E} {Λ : Submodule (𝓞
  E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ} {Om : GAF σ JS × GAF σ
  JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)} {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
private theorem sgsg_pk (hB : GoodK σ B) (x : E) : σ (σ x) = x := by
  let τ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  exact τ.injective (by rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star])

private def ratEquivF_pk (C : Ctx_k σ B JS JT ξ₀ θ ι) : Matrix (Fin nT) (Fin nS) E ≃ ratLF F E nS nT :=
  Equiv.ofBijective (fun y => ⟨ratWF y, y, rfl⟩)
    ⟨fun _ _ h => _root_.PositivityTheory.ThKW.TauSpanIdentities.infRatF_injective B (by
      have h' : ratWF _ = ratWF _ := congrArg Subtype.val h
      rw [← piWF_ratWF_k C, ← piWF_ratWF_k C, h']),
     by rintro ⟨_, y, rfl⟩; exact ⟨y, rfl⟩⟩

private theorem serF_eq_pk (C : Ctx_k σ B JS JT ξ₀ θ ι) (a : IxF F nS nT → ℂ) (x : WOF F E nS nT) :
    serF σ JS JT ξ₀ B θ ι s Λ w a x = ∑' y : Matrix (Fin nT) (Fin nS) E,
      B.ψ (symplOHF σ JS JT ξ₀ (ratWF y) x) * B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι a) (ratWF y + x)) *
        chiLatF σ JS JT ξ₀ B.ψ Λ w (ratWF y + x) *
        exp (-(pi / 2 : ℂ) * (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y + (a + piWF θ x))
          (jV s (infRatF (tauB B) y + (a + piWF θ x))) : ℝ)) := by
  unfold serF GlobalTheory.HeisenbergGaussianSeries.series
  rw [← (ratEquivF_pk C).tsum_eq]
  have hc' (y : Matrix (Fin nT) (Fin nS) E) : ((ratEquivF_pk C y : ratLF F E nS nT) : WOF F E nS nT) = ratWF y := rfl
  simp only [hc', piWA_apply, iotaA_apply, piWF_ratWF_k C]

private theorem chi_add_lat_pk (C : Ctx_k σ B JS JT ξ₀ θ ι) (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ))
    (hw : w + sgOF σ w = 1) {u : XFF F E nS nT} (hu : u ∈ latF F E nS nT Λ) (x : WOF F E nS nT) :
    phaseF σ JS JT ξ₀ B.ψ w u * (B.ψ (symplOHF σ JS JT ξ₀ x u) * chiLatF σ JS JT ξ₀ B.ψ Λ w (x + u)) =
      chiLatF σ JS JT ξ₀ B.ψ Λ w x := by
  have e : finIdem F E • (x + (u : WOF F E nS nT)) = finIdem F E • x + u := by
    rw [smul_add, _root_.PositivityTheory.ThKW.TauSpanIdentities.finIdem_smul_of_fin u.fin]
  have e2 : B.ψ (symplOHF σ JS JT ξ₀ x u) = B.ψ (symplOHF σ JS JT ξ₀ (finIdem F E • x) u) := by
    have h3 := beta_iota_left_k C (piWF θ x) (u : WOF F E nS nT)
    rw [_root_.PositivityTheory.ThKW.TauSpanIdentities.piWF_of_fin u.fin, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h3
    conv_lhs => rw [finIdem_add_iota C.chart x]
    rw [symplOHF_add_left, map_add_eq_mul, h3, mul_one]
  unfold chiLatF; rw [e, e2]
  have hy := finIdem_smul_fin x
  generalize finIdem F E • x = y at hy ⊢
  by_cases h : y ∈ latOF F E nS nT Λ
  · rw [ite_eq_left h, ite_eq_left (add_mem h hu)]
    have h0 : B.ψ (symplOF σ JS JT ξ₀ (intAF F w • y) u) = 1 :=
      (hA _).1 ((latF F E nS nT Λ).smul_mem w (show XFF.mk y hy ∈ latF F E nS nT Λ from h)) u hu
    rw [phaseF, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad (sgsg_pk C.good) C.hS C.hT C.hξ hw,
      AddChar.map_add_eq_mul, h0, mul_one]
  · have h2 : y + (u : WOF F E nS nT) ∉ latOF F E nS nT Λ := fun h' => h (by
      have h3 := sub_mem h' (mem_latF.1 hu); rwa [add_sub_cancel_right] at h3)
    rw [ite_eq_right h, ite_eq_right h2, mul_zero, mul_zero]

private theorem ser_vac_pk (C : Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s)
    (a : IxF F nS nT → ℂ) :
    ∃ hf : IsThetaFunOF σ JS JT ξ₀ B.ψ (serF σ JS JT ξ₀ B θ ι s Λ w a),
      Fixes (opFF hc w) (latF F E nS nT Λ) (⟨_, hf⟩ : thetaSubF σ JS JT ξ₀ B.ψ) ∧
      IsVacF σ JS JT ξ₀ B.ψ ι s (serF σ JS JT ξ₀ B θ ι s Λ w a) := by
  have hσ := sgsg_pk C.good
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B C.good).1
  have hA := hO.sd; have hw := hO.hw
  obtain ⟨-, hJ, hsym, hpos⟩ := _root_.PositivityTheory.ThKW.TauSpanIdentities.omV_laws
    (hermitian_form_selfadjoint_global F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ).1 hs.sq hs.pos
  have hl : ∀ x y z : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ (x + y) z) =
      B.ψ (symplOHF σ JS JT ξ₀ x z) * B.ψ (symplOHF σ JS JT ξ₀ y z) :=
    fun _ _ _ => by rw [symplOHF_add_left, AddChar.map_add_eq_mul]
  have hr : ∀ x y z : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ x (y + z)) =
      B.ψ (symplOHF σ JS JT ξ₀ x y) * B.ψ (symplOHF σ JS JT ξ₀ x z) :=
    fun _ _ _ => by rw [symplOHF_add_right, AddChar.map_add_eq_mul]
  have hd : ∀ x : WOF F E nS nT, B.ψ (symplOHF σ JS JT ξ₀ x x) = 1 := fun _ => by
    rw [symplOHF, GlobalTheory.HeisLineF.symplOF_self σ JS JT hσ C.hS C.hT ξ₀ C.hξ, mul_zero, AddChar.map_zero_eq_one]
  have hβ : ∀ (x : WOF F E nS nT) (v : IxF F nS nT → ℂ), B.ψ (symplOHF σ JS JT ξ₀ x (iotaA ι v)) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWA θ x) v : ℝ)) :=
    fun x v => beta_iota_right_k C x v
  have fl : ∀ u ∈ latF F E nS nT Λ, ∀ x : WOF F E nS nT, phaseF σ JS JT ξ₀ B.ψ w u *
      (B.ψ (symplOHF σ JS JT ξ₀ x u) * serF σ JS JT ξ₀ B θ ι s Λ w a (x + u)) = serF σ JS JT ξ₀ B θ ι s Λ w a x :=
    fun u hu x => GlobalTheory.GaussSeriesVacuum.series_inv_scalar (G := WOF F E nS nT)
      (β := fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) hl hr hd hβ a u (_root_.PositivityTheory.ThKW.TauSpanIdentities.piWF_of_fin u.fin) _
      (chi_add_lat_pk C hA hw hu) x
  obtain ⟨U, hUo, hlev⟩ := exists_level (F := F) (E := E) (nS := nS) (nT := nT) hG 2 two_pos
  let U₀ : AddSubgroup (WOF F E nS nT) :=
    (latOF F E nS nT Λ).comap (DistribSMul.toAddMonoidHom (WOF F E nS nT) (finIdem F E))
  obtain ⟨fc, fs, fv⟩ := GlobalTheory.GaussSeriesVacuum.series_regular (piWA θ) (iotaA ι)
    (fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) (omV (HMF JS JT ξ₀ (tauB B))) (jV s) (ratLF F E nS nT) U₀ U
    (chiLatF σ JS JT ξ₀ B.ψ Λ w) (continuous_piWF_k C) (continuous_iotaVF C.chart) (piWF_iotaVF C.chart) hl hr hd
    (fun _ _ => hψ.2.1 _) (hψ.1.comp (continuous_symplOHF σ JS JT ξ₀ continuous_fst continuous_snd))
    hβ hJ hsym hpos
    (by
      rintro _ ⟨y, rfl⟩ h
      have e : piWF θ (ratWF (F := F) y) = 0 := h
      rw [piWF_ratWF_k C] at e
      have : y = 0 := _root_.PositivityTheory.ThKW.TauSpanIdentities.infRatF_injective B (by rw [e, map_zero])
      subst this; exact map_zero _)
    (fun R => by
      refine ((finite_lat_k C.good hG R).image (fun y => ratWF (F := F) y)).subset ?_
      rintro _ ⟨⟨y, rfl⟩, h1, h2⟩
      exact ⟨y, ⟨(finRatF_mem_iff_k C hG hR hA y).1 h1, by
        have e : piWF θ (ratWF (F := F) y) = infRatF (tauB B) y := piWF_ratWF_k C y
        rw [← e]; exact h2⟩, rfl⟩)
    (fun _ hx => by unfold chiLatF; exact ite_eq_right hx)
    (fun x => by unfold chiLatF; split_ifs; exacts [(hψ.2.1 _).le, by rw [norm_zero]; exact zero_le_one])
    (fun x v => by
      show chiLatF σ JS JT ξ₀ B.ψ Λ w (x + iotaVF ι v) = _
      unfold chiLatF; rw [smul_add, _root_.PositivityTheory.ThKW.TauSpanIdentities.finIdem_smul_of_real (real_iotaVF C.chart v), add_zero])
    hUo
    (fun u hu x => by
      obtain ⟨l, hl', e⟩ := hlev u hu
      have e3 : u - iotaA ι (piWA θ u) = ((2 • l : XFF F E nS nT) : WOF F E nS nT) :=
        (sub_eq_of_eq_add (finIdem_add_iota C.chart u)).trans e
      rw [e3]
      have e2 := chi_add_lat_pk C hA hw (nsmul_mem hl' 2) x
      rw [phase_two' hA w hl', one_mul] at e2; exact e2) a
  have hquasi : ∀ (γ : Matrix (Fin nT) (Fin nS) E) (x : WOF F E nS nT),
      serF σ JS JT ξ₀ B θ ι s Λ w a (ratWF γ + x) =
        B.ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) x)) * serF σ JS JT ξ₀ B θ ι s Λ w a x := fun γ x => by
    have e : B.ψ (symplOHF σ JS JT ξ₀ (ratWF γ) x) * serF σ JS JT ξ₀ B θ ι s Λ w a (ratWF γ + x) =
        serF σ JS JT ξ₀ B θ ι s Λ w a x :=
      GlobalTheory.HeisenbergGaussianSeries.series_quasi (G := WOF F E nS nT) (p := piWA θ) (ι := iotaA ι)
        (β := fun x y => B.ψ (symplOHF σ JS JT ξ₀ x y)) (om := omV (HMF JS JT ξ₀ (tauB B))) (J := jV s)
        (Γ := ratLF F E nS nT) (χ := chiLatF σ JS JT ξ₀ B.ψ Λ w) hl hr
        (by rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩; exact psi_rat_k C y y') a (ratWF γ) ⟨γ, rfl⟩ x
    rw [← e, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  have hlevel : ∀ u ∈ U, u.map (infPartF F E) = 0 →
      heisOF σ JS JT ξ₀ B.ψ u (serF σ JS JT ξ₀ B θ ι s Λ w a) = serF σ JS JT ξ₀ B θ ι s Λ w a := fun u hu h => by
    obtain ⟨l, hl', e⟩ := hlev u hu; rw [_root_.PositivityTheory.ThKW.TauSpanIdentities.finIdem_smul_of_fin h] at e; subst e
    funext x; have e2 := fl _ (nsmul_mem hl' 2) x; rw [phase_two' hA w hl', one_mul] at e2; exact e2
  have hsm : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L → (∀ t, (L t).map (finPartF F E) = 0) →
      ∀ x, ContDiff ℝ ∞ fun t => serF σ JS JT ξ₀ B θ ι s Λ w a (x + L t) := fun k L hL hL0 x => by
    let c : (Fin k → ℝ) →+ (IxF F nS nT → ℂ) := (piWA θ).comp L
    have hLc : ∀ t, L t = iotaA ι (c t) := fun t => by
      have := finIdem_add_iota C.chart (L t); rwa [_root_.PositivityTheory.ThKW.TauSpanIdentities.finIdem_smul_of_real (hL0 t), zero_add] at this
    exact (congrArg (ContDiff ℝ ∞) (funext fun t => by
      show _ = serF σ JS JT ξ₀ B θ ι s Λ w a (x + L t); rw [hLc t]; rfl)).mp
      ((fs x).comp (c.toRealLinearMap ((continuous_piWF_k C).comp hL)).contDiff)
  refine ⟨⟨hquasi, ⟨U, hUo, hlevel⟩, fc, hsm⟩,
    fun u hu => Subtype.ext (funext fun x => by rw [coe_opFF]; exact fl u hu x), fun x z => fv x z⟩

private theorem summable_coefQF_pk (C : Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ))
    (hpos : ∀ v, v ≠ 0 → 0 < omV (HMF JS JT ξ₀ (tauB B)) v (jV s v)) (w : 𝓞 E) (u : XFF F E nS nT) :
    Summable fun y => ‖coefQF σ JS JT ξ₀ B s Λ w u y‖ := by
  have hψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B C.good).1
  have h := GlobalTheory.HeisenbergGaussianSeries.summable_coeff (G := WOF F E nS nT) (piWA θ)
    (omV (HMF JS JT ξ₀ (tauB B))) (jV s) (ratLF F E nS nT)
    ((latOF F E nS nT Λ).comap (DistribSMul.toAddMonoidHom (WOF F E nS nT) (finIdem F E)))
    (chiLatF σ JS JT ξ₀ B.ψ Λ w) hpos
    (by
      rintro _ ⟨y, rfl⟩ hy
      have e : piWF θ (ratWF (F := F) y) = 0 := hy
      rw [piWF_ratWF_k C] at e
      have : y = 0 := _root_.PositivityTheory.ThKW.TauSpanIdentities.infRatF_injective B (by rw [e, map_zero])
      subst this; exact map_zero _)
    (fun R => by
      refine ((finite_lat_k C.good hG R).image (fun y => ratWF y)).subset ?_
      rintro _ ⟨⟨y, rfl⟩, h1, h2⟩
      refine ⟨y, ⟨(finRatF_mem_iff_k C hG hR hA y).1 h1, ?_⟩, rfl⟩
      have e := piWF_ratWF_k C y
      rw [← e]; exact h2)
    (fun _ hx => ite_eq_right hx) (fun x => by unfold chiLatF; split_ifs; exacts [(hψ.2.1 _).le, by simp])
    (fun y => B.ψ (symplOHF σ JS JT ξ₀ y u)) (fun _ => hψ.2.1 _) u 0 0 0
  rw [← (ratEquivF_pk C).summable_iff] at h
  refine h.congr fun y => ?_
  have e : ‖phaseF σ JS JT ξ₀ B.ψ w u‖ = 1 := hψ.2.1 _
  have hc' (y : Matrix (Fin nT) (Fin nS) E) : ((ratEquivF_pk C y : ratLF F E nS nT) : WOF F E nS nT) = ratWF y := rfl
  simp only [Function.comp_apply, hc', piWA_apply, piWF_ratWF_k C, add_zero, zero_mul, Real.exp_zero, mul_one]
  rw [coefQF, norm_mul (phaseF σ JS JT ξ₀ B.ψ w u), e, one_mul]

theorem gauss_mul_integral_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS}
    {h : GAF σ JT} {a b} (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (hbij : Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x))
    (hF : Integrable (gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹))) volume) (κ : ℂ)
    (hκ : ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, Fixes (opFF hc w) (latF F E nS nT Λ) f → IsVacF σ JS JT ξ₀ B.ψ ι s f → ∀ x,
      (f : WOF F E nS nT → ℂ) (actOF σ JS JT g⁻¹ h⁻¹ x) = κ * ((sumOp (opFF hc w) (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) f : thetaSubF σ JS JT ξ₀ B.ψ) : WOF F E nS nT → ℂ) x)
    (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (ht : ∀ k, b * t k * a - t k ∈ Λ)
    (hu : ∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) :
    ∃ r : ℝ, 0 < r ∧ (∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k)) *
      ∫ v, gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) v = r * κ := by
  have hσ := sgsg_pk C.good
  obtain ⟨hH, -⟩ := hermitian_form_selfadjoint_global F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ
  obtain ⟨halt, -, -, hpos⟩ := _root_.PositivityTheory.ThKW.TauSpanIdentities.omV_laws (H := HMF JS JT ξ₀ (tauB B)) hH hs.sq hs.pos
  have hw := hO.hw; have H := isHeis_opFF hσ C.hS C.hT C.hξ hc hw
  have hA := hO.sd; have hB := hO.sd' (g, h)
  have hmem : ∀ y, finRatF F y ∈ latF F E nS nT Λ ↔ y ∈ Λ := finRatF_mem_iff_k C hG hR hA
  have hiota : ∀ v : IxF F nS nT → ℂ, (iotaVF ι v).map (finPartF F E) = 0 :=
    fun _ => funext fun _ => funext fun _ => C.chart.fin _
  have hsymAct : ∀ (g' : GAF σ JS) (h' : GAF σ JT) (x y : WOF F E nS nT),
      symplOHF σ JS JT ξ₀ (actOF σ JS JT g' h' x) (actOF σ JS JT g' h' y) = symplOHF σ JS JT ξ₀ x y :=
    fun _ _ _ _ => by unfold symplOHF; rw [symplOF_actOF_k C]
  have hchiI : ∀ x v, chiLatF σ JS JT ξ₀ B.ψ Λ w (x + iotaVF ι v) = chiLatF σ JS JT ξ₀ B.ψ Λ w x := fun _ v => by
    unfold chiLatF; rw [smul_add, _root_.PositivityTheory.ThKW.TauSpanIdentities.finIdem_smul_of_real (hiota v), add_zero]
  have hactI : ∀ v : IxF F nS nT → ℂ, actOF σ JS JT g⁻¹ h⁻¹ (iotaVF ι v) = iotaVF ι (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) :=
    fun v => by
      have e := finIdem_add_iota C.chart (actOF σ JS JT g⁻¹ h⁻¹ (iotaVF ι v))
      rwa [← actOF_smul, _root_.PositivityTheory.ThKW.TauSpanIdentities.finIdem_smul_of_real (hiota v), actOF_zero', zero_add, piWF_actOF_k C,
        piWF_iotaVF C.chart] at e
  have hactR : ∀ y v, mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ (infRatF (tauB B) y + v) =
      infRatF (tauB B) (b * y * a) + mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v := fun y _ => by
    rw [mulVec_add, ← piWF_ratWF_k C y, ← piWF_ratWF_k C (b * y * a), ← act_ratW ha hb, piWF_actOF_k C]
  have homAct : ∀ u v, omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) =
      omV (HMF JS JT ξ₀ (tauB B)) u v := fun u v => by
    set A := omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v)
    set B' := omV (HMF JS JT ξ₀ (tauB B)) u v
    have key : ∀ t : ℝ, Complex.exp (-(Real.pi * Complex.I) * ((t * A : ℝ) : ℂ)) =
        Complex.exp (-(Real.pi * Complex.I) * ((t * B' : ℝ) : ℂ)) := fun t => by
      have h1 := beta_iota_left_k C (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ (t • u)) (actOF σ JS JT g⁻¹ h⁻¹ (iotaVF ι v))
      have h2 := beta_iota_left_k C (t • u) (iotaVF ι v)
      rw [piWF_actOF_k C, piWF_iotaVF C.chart, ← hactI, hsymAct] at h1
      rw [piWF_iotaVF C.chart] at h2
      have h3 := h1.symm.trans h2
      rwa [mulVec_smul, map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h3
    by_contra hne
    have hd : A - B' ≠ 0 := sub_ne_zero.2 hne
    have k2 := Complex.exp_sub (-(Real.pi * Complex.I) * (((A - B')⁻¹ * A : ℝ) : ℂ))
      (-(Real.pi * Complex.I) * (((A - B')⁻¹ * B' : ℝ) : ℂ))
    rw [key (A - B')⁻¹, div_self (Complex.exp_ne_zero _),
      show -(Real.pi * Complex.I) * (((A - B')⁻¹ * A : ℝ) : ℂ) -
        -(Real.pi * Complex.I) * (((A - B')⁻¹ * B' : ℝ) : ℂ) = -(Real.pi * Complex.I) by
        rw [← mul_sub, ← Complex.ofReal_sub, ← mul_sub, inv_mul_cancel₀ hd, Complex.ofReal_one, mul_one],
      Complex.exp_neg, Complex.exp_pi_mul_I] at k2
    norm_num at k2
  have hleft : ∀ v : IxF F nS nT → ℂ, serF σ JS JT ξ₀ B θ ι s Λ w (-v) (actOF σ JS JT g⁻¹ h⁻¹ (iotaVF ι v)) =
      ∑' y, gaussQF σ JS JT ξ₀ B.ψ Λ w a b y *
        gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) (infRatF (tauB B) y + v) := fun v => by
    rw [hactI, serF_eq_pk C, ← (Equiv.ofBijective _ hbij).tsum_eq]
    refine tsum_congr fun y => ?_
    have h0 := homAct (infRatF (tauB B) y) v
    have h1 := hactR y 0; rw [mulVec_zero, add_zero, add_zero] at h1; rw [h1] at h0
    have hchiM : chiLatF σ JS JT ξ₀ B.ψ Λ w (ratWF (b * y * a - y)) = gaussQF σ JS JT ξ₀ B.ψ Λ w a b y *
        Complex.exp (-(Real.pi * Complex.I) *
          (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) (b * y * a)) (infRatF (tauB B) y) : ℝ)) := by
      have hm : ∀ z, finIdem F E • ratWF (F := F) z ∈ latOF F E nS nT Λ ↔ z ∈ Λ := fun z =>
        finRatF_mem_iff_k C hG hR hA z
      unfold chiLatF gaussQF
      by_cases hy : b * y * a - y ∈ Λ
      · rw [ite_eq_left ((hm _).2 hy), ite_eq_left hy]
        show B.ψ (symplOHF σ JS JT ξ₀ (intAF F w • (finRatF F (b * y * a - y) : WOF F E nS nT))
          (finRatF F (b * y * a - y))) = _
        have e : (finRatF F (b * y * a - y) : WOF F E nS nT) + finRatF F y = finRatF F (b * y * a) := by
          rw [← XFF.coe_add, ← map_add (f := _), sub_add_cancel]
        have hW : intAF F w + cAF σ (intAF F w) = 1 := by rw [cAF_intAF, ← map_add (f := _), hw, map_one]
        have hi : symplOHF σ JS JT ξ₀ (intAF F w • ((finRatF F (b * y * a - y) : WOF F E nS nT) + finRatF F y))
            ((finRatF F (b * y * a - y) : WOF F E nS nT) + finRatF F y) =
            symplOHF σ JS JT ξ₀ (intAF F w • (finRatF F y : WOF F E nS nT)) (finRatF F y) := by
          rw [e, ← act_finRat ha hb, ← actOF_smul, hsymAct]
        have hp : symplOHF σ JS JT ξ₀ (intAF F w • (finRatF F (b * y * a - y) : WOF F E nS nT))
            (finRatF F (b * y * a - y)) + symplOHF σ JS JT ξ₀ ((finRatF F (b * y * a - y) : WOF F E nS nT) +
            finRatF F y) (finRatF F y) = symplOF σ JS JT ξ₀ (cAF σ (intAF F w) • (finRatF F (b * y * a - y) :
            WOF F E nS nT)) (finRatF F y) := by
          have p1 : symplOHF σ JS JT ξ₀ (finRatF F y : WOF F E nS nT) (finRatF F y) = 0 := by
            unfold symplOHF; rw [GlobalTheory.HeisLineF.symplOF_self σ JS JT hσ C.hS C.hT ξ₀ C.hξ, mul_zero]
          have p2 : symplOHF σ JS JT ξ₀ (finRatF F (b * y * a - y) : WOF F E nS nT) (finRatF F y) =
              symplOHF σ JS JT ξ₀ (intAF F w • (finRatF F (b * y * a - y) : WOF F E nS nT)) (finRatF F y) +
              symplOHF σ JS JT ξ₀ (cAF σ (intAF F w) • (finRatF F (b * y * a - y) : WOF F E nS nT)) (finRatF F y) := by
            rw [← symplOHF_add_left, ← add_smul, hW, one_smul]
          have p3 : symplOHF σ JS JT ξ₀ (intAF F w • (finRatF F y : WOF F E nS nT)) (finRatF F (b * y * a - y)) =
              -symplOHF σ JS JT ξ₀ (cAF σ (intAF F w) • (finRatF F (b * y * a - y) : WOF F E nS nT)) (finRatF F y) := by
            rw [symplOHF_smul σ JS JT hσ, symplOHF_skew σ JS JT hσ C.hS C.hT ξ₀ C.hξ]
          rw [smul_add, symplOHF_add_left, symplOHF_add_right, symplOHF_add_right] at hi
          rw [symplOHF_add_left, ← symplOHF_add_self]; linear_combination hi + p1 + p2 - p3
        have hbf : B.ψ (symplOHF σ JS JT ξ₀ (finRatF F (b * y * a) : WOF F E nS nT) (finRatF F y)) *
            Complex.exp (-(Real.pi * Complex.I) *
              (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) (b * y * a)) (infRatF (tauB B) y) : ℝ)) = 1 := by
          have b1 := psi_rat_k C (b * y * a) y
          have b2 := beta_iota_left_k C (infRatF (tauB B) (b * y * a)) (ratWF (F := F) y)
          have b3 := beta_iota_right_k C (finRatF F (b * y * a) : WOF F E nS nT) (infRatF (tauB B) y)
          rw [piWF_of_fin (finRatF F _).fin, LinearMap.map_zero, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero,
            Complex.exp_zero] at b3
          have rEq : ∀ z, ratWF (F := F) z = iotaVF ι (infRatF (tauB B) z) + (finRatF F z : WOF F E nS nT) := fun z =>
            by rw [add_comm, ← piWF_ratWF_k C z]; exact finIdem_add_iota C.chart _
          have d1 : symplOHF σ JS JT ξ₀ (ratWF (b * y * a)) (ratWF y) =
              symplOHF σ JS JT ξ₀ (iotaVF ι (infRatF (tauB B) (b * y * a))) (ratWF y) +
              symplOHF σ JS JT ξ₀ (finRatF F (b * y * a) : WOF F E nS nT) (ratWF y) := by
            rw [← symplOHF_add_left, ← rEq]
          have d2 : symplOHF σ JS JT ξ₀ (finRatF F (b * y * a) : WOF F E nS nT) (ratWF y) =
              symplOHF σ JS JT ξ₀ (finRatF F (b * y * a) : WOF F E nS nT) (iotaVF ι (infRatF (tauB B) y)) +
              symplOHF σ JS JT ξ₀ (finRatF F (b * y * a) : WOF F E nS nT) (finRatF F y) := by
            rw [← symplOHF_add_right, ← rEq]
          rwa [d1, d2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, b2, b3, one_mul, mul_comm, piWF_ratWF_k C] at b1
        have h2 : gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * y * a - y)) y =
            B.ψ (symplOF σ JS JT ξ₀ (cAF σ (intAF F w) • (finRatF F (b * y * a - y) : WOF F E nS nT)) (finRatF F y)) :=
          by rw [gamQF, gamFF, map_smul, cAF_intAF]; rfl
        rw [h2, ← hp, e, AddChar.map_add_eq_mul, mul_assoc, hbf, mul_one]
      · rw [ite_eq_right (fun h => hy ((hm _).1 h)), ite_eq_right hy, zero_mul]
    rw [Equiv.ofBijective_apply, hchiI, hchiM, beta_iota_right_k C, beta_iota_left_k C, gaussV, hactR, piWF_add,
      piWF_iotaVF C.chart, piWF_ratWF_k C, map_sub (infRatF (tauB B))]
    generalize mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v = u at h0 ⊢
    generalize infRatF (tauB B) (b * y * a) = z at h0 ⊢
    generalize infRatF (tauB B) y = x at h0 ⊢
    have e2 : Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (z - x) u : ℝ)) *
        Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (-v) (z - x + u) : ℝ)) *
        Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) z x : ℝ)) =
        Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (z + u) (x + v) : ℝ)) := by
      rw [← Complex.exp_add, ← Complex.exp_add, ← mul_add, ← mul_add, ← Complex.ofReal_add, ← Complex.ofReal_add]
      congr 3
      simp only [map_add (f := _), map_sub, map_neg, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply]
      linarith [halt x u, halt v z, halt v x, halt v u]
    rw [show z - x + (-v + u) = z + u - (x + v) by abel, ← e2]; ring
  have hright : ∀ (u : XFF F E nS nT) (v : IxF F nS nT → ℂ),
      (phaseF σ JS JT ξ₀ B.ψ w u • heisOF σ JS JT ξ₀ B.ψ u (serF σ JS JT ξ₀ B θ ι s Λ w (-v))) (iotaVF ι v) =
        ∑' y, coefQF σ JS JT ξ₀ B s Λ w u y *
          Complex.exp (2 * Real.pi * Complex.I * ((-omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) v : ℝ)) := by
    intro u v
    have hu' : piWF θ (u : WOF F E nS nT) = 0 := piWF_of_fin u.fin
    rw [Pi.smul_apply, smul_eq_mul, heisOF, beta_iota_left_k C, hu', LinearMap.map_zero, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_mul, serF_eq_pk C, ← tsum_mul_left]
    refine tsum_congr fun y => ?_
    have e2 : omV (HMF JS JT ξ₀ (tauB B)) v v = 0 := by linarith [halt v v]
    have e3 : Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y) v : ℝ)) *
        Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (-v) (infRatF (tauB B) y + v) : ℝ)) =
        Complex.exp (2 * Real.pi * Complex.I * ((-omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) v : ℝ)) := by
      rw [← Complex.exp_add]; congr 1
      simp only [map_add (f := _), map_neg, LinearMap.neg_apply, e2, halt v (infRatF (tauB B) y)]; push_cast; ring
    rw [coefQF, symplOHF_add_right, AddChar.map_add_eq_mul, beta_iota_right_k C, beta_iota_left_k C, piWF_add, piWF_add,
      hu', piWF_iotaVF C.chart, piWF_ratWF_k C, add_zero, neg_add_cancel, add_zero,
      show ratWF (F := F) y + (iotaVF ι v + (u : WOF F E nS nT)) = (ratWF y + (u : WOF F E nS nT)) + iotaVF ι v by abel,
      hchiI, ← e3]; ring
  obtain ⟨m, u, huB, huT⟩ := exists_transversal_of_idx_ne_zero _ _ (hO.fin (g, h))
  let Cg : AddSubgroup (Matrix (Fin nT) (Fin nS) E) := Λ.toAddSubgroup ⊓ Λ.toAddSubgroup.comap (sandF b a)
  have hC : ∀ x, x ∈ Cg ↔ x ∈ Λ ∧ b * x * a ∈ Λ := fun _ => Iff.rfl
  have hQ : ∀ y, b * y * a - y ∈ Λ → gaussQF σ JS JT ξ₀ B.ψ Λ w a b y =
      gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * y * a - y)) y := fun _ hy => ite_eq_left hy
  have hQ0 : ∀ y, b * y * a - y ∉ Λ → gaussQF σ JS JT ξ₀ B.ψ Λ w a b y = 0 := fun _ hy => ite_eq_right hy
  have h0 : κ * ∑ i, coefQF σ JS JT ξ₀ B s Λ w (u i) 0 = κ := by
    obtain ⟨i, hi, hi'⟩ := huT 0 (zero_mem _)
    rw [Finset.sum_eq_single i, coefQF_zero w (by simpa using hi), mul_one]
    · intro j _ hj; by_contra hn; exact hj (hi' j (by simpa using mem_of_coefQF_ne_zero hn))
    · exact fun hn => (hn (Finset.mem_univ _)).elim
  obtain ⟨r, hr, e⟩ := _root_.GlobalTheory.PoincareUnfold.unfold_poincare_fourier (IxF F nS nT → ℂ) volume _
    (infRatF (tauB B)) (_root_.PositivityTheory.ThKW.TauSpanIdentities.infRatF_injective B) Cg
    (fun R => (finite_lat_k C.good hG R).subset fun c hc => ⟨((hC c).1 hc.1).1, hc.2⟩)
    (by
      rw [eq_top_iff, ← span_infRatF_k C.good, Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      obtain ⟨N, hN, h1⟩ := hG.den y; obtain ⟨M, hM, h2⟩ := hG.den (b * y * a)
      have h3 : (M * N) • y ∈ Cg := (hC _).2 ⟨by rw [mul_smul]; exact Submodule.smul_of_tower_mem Λ M h1, by
        rw [show b * ((M * N) • y) * a = (N * M) • (b * y * a) by rw [Matrix.mul_smul, Matrix.smul_mul, mul_comm],
          mul_smul]; exact Submodule.smul_of_tower_mem Λ N h2⟩
      rw [show infRatF (tauB B) y = ((M * N : ℕ) : ℝ)⁻¹ • infRatF (tauB B) ((M * N) • y) by
        rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (Nat.cast_ne_zero.2 (Nat.mul_pos hM hN).ne')]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h3, rfl⟩))
    n t (gaussQF σ JS JT ξ₀ B.ψ Λ w a b)
    (fun y hy => by
      have h1 : b * y * a - y ∈ Λ := by_contra fun hn => hy (hQ0 y hn)
      obtain ⟨k, hk, -⟩ := hu y h1
      refine ⟨k, (hC _).2 ⟨hk, ?_⟩⟩
      rw [show b * (y - t k) * a = (b * y * a - y) - (b * t k * a - t k) + (y - t k) by
        rw [Matrix.mul_sub, Matrix.sub_mul]; abel]
      exact add_mem (sub_mem h1 (ht k)) hk)
    (fun k _ hk => (hu (t k) (ht k)).unique (by rw [sub_self]; exact zero_mem _) ((hC _).1 hk).1)
    (fun y c hc => by
      obtain ⟨hc1, hc2⟩ := (hC c).1 hc
      have e : b * (y + c) * a - (y + c) = (b * y * a - y) + (b * c * a - c) := by
        rw [Matrix.mul_add, Matrix.add_mul]; abel
      have hc' : b * c * a - c ∈ Λ := sub_mem hc2 hc1
      by_cases hy : b * y * a - y ∈ Λ
      · rw [hQ _ hy, hQ _ (e ▸ add_mem hy hc'), gamQF, gamQF, map_smul, map_smul, map_sub, map_sub,
          ← _root_.PositivityTheory.ThKW.TauSpanIdentities.rhoFF_finRatF ha hb, ← _root_.PositivityTheory.ThKW.TauSpanIdentities.rhoFF_finRatF ha hb, map_add (finRatF F)]
        exact _root_.GlobalTheory.RatTrace.gam_periodic H hA _ (fun _ _ => by unfold gamFF; rw [coe_rhoFF, coe_rhoFF, symplOF_actOF_k C]) _
          (by rw [_root_.PositivityTheory.ThKW.TauSpanIdentities.rhoFF_finRatF ha hb, ← map_sub]; exact (hmem _).2 hy) ((hmem c).2 hc1)
          (by rw [_root_.PositivityTheory.ThKW.TauSpanIdentities.rhoFF_finRatF ha hb]; exact (hmem _).2 hc2)
      · rw [hQ0 _ hy, hQ0]; intro hn; rw [e] at hn; exact hy ((add_mem_cancel_right hc').1 hn))
    _ hF (fun y => κ * ∑ i, coefQF σ JS JT ξ₀ B s Λ w (u i) y)
    (fun y => -omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y))
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun y => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _))
      ((summable_sum fun i (_ : i ∈ Finset.univ) => summable_coefQF_pk C hG hR hA hpos w (u i)).mul_left ‖κ‖))
    (by simp)
    (fun y hy hn => by
      have h2 := hpos _ (fun h => hy (_root_.PositivityTheory.ThKW.TauSpanIdentities.infRatF_injective B (h.trans (map_zero _).symm)))
      rw [neg_eq_zero.1 hn] at h2; exact lt_irrefl _ h2)
    (fun y hy c hc => by
      obtain ⟨hc1, hc2⟩ := (hC c).1 hc
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hy)
      have h1 : finRatF F c ∈ (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)) :=
        ⟨finRatF F (b * c * a), (hmem _).2 hc2, by
          rw [← _root_.PositivityTheory.ThKW.TauSpanIdentities.rhoFF_finRatF ha hb, ← mul_apply_eq_comp, ← map_mul,
            show ((g, h) : GAF σ JS × GAF σ JT) * (g⁻¹, h⁻¹) = 1 from mul_inv_cancel (g, h), map_one,
            one_apply_eq_self]⟩
      have h2 := H.iso hA (mem_of_coefQF_ne_zero hi) ((hmem c).2 hc1)
      rw [H.add_left, H.iso hB (huB i) h1, mul_one] at h2
      obtain ⟨z, hz⟩ := (gamQF_eq_one_iff_k C y c).1 h2
      exact ⟨-z, by rw [LinearMap.neg_apply, hz, Int.cast_neg]⟩)
    (fun v => by
      obtain ⟨hf, hfix, hvac⟩ := ser_vac_pk C hG hR hO hs (-v)
      have e := hκ ⟨_, hf⟩ hfix hvac (iotaVF ι v)
      rw [(sumOp_eq_sum_transversal H _ _ hB _ hfix _ u huB huT).1, Submodule.coe_sum, Finset.sum_apply] at e
      simp only [coe_opFF, hright, hleft] at e
      rw [e, ← Summable.tsum_finsetSum, ← tsum_mul_left]
      · exact tsum_congr fun y => by rw [← Finset.sum_mul, mul_assoc κ]
      · intro i _
        refine Summable.of_norm ((summable_coefQF_pk C hG hR hA hpos w (u i)).congr fun y => ?_)
        have e1 : (2 * Real.pi * Complex.I *
            ((-omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) v : ℝ) : ℂ) =
            ((2 * Real.pi * (-omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) v : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [norm_mul, e1, Complex.norm_exp_ofReal_mul_I, mul_one])
  rw [h0, Finset.sum_congr rfl fun k _ => hQ _ (ht k)] at e
  exact ⟨r, hr, e⟩
end PositivityTheory.ThKW
end
