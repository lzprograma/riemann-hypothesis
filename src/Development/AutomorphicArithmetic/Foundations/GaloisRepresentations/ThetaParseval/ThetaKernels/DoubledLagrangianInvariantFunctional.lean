module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformAdelicSchwartzRealDirection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformArchimedeanCm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsTransferHaarFundamentalDomainCm
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainRationalMatricesTower
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLintegralSqEqMulSetLIntegralThetaTransformStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairPartnerInverseTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTransportCmPreservesAdmissibleForms
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledLagrangianContinuous
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledLagrangianUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffTsumOfLocallySummableBounds
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableRationalSchwartzBruhatMulPolynomialDecayStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariantCm

/-! # DoubledLagrangianInvariantFunctional: Consolidated global theta-kernel definitions and proofs (DoubledLagrangianInvariantFunctional). -/
@[expose] public section

open GlobalTheory.WeilSchrodinger (thetaTr)
open UpperTheory.TP.W (GoodK)
open scoped TensorProduct Matrix
open Formalism.IndefR.DatumF (IsHeckeCharF IsWeilDatumOF ResEtaF)
open Formalism.IndefR.DatumF (GAF IsStdCharF WOF)

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
namespace GlobalTheory.ThetaTrContF
theorem continuous_thetaTrF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E) (B : Base F E),
    GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, Continuous (thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ _ _ κ _ co _ Φ hΦ
  have : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (AE
    (F := F) (E := E))) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS →
      AE (F := F) (E := E)))
  have hc : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  exact (GlobalTheory.ThetaTrCont.schA_cont F B.ψ hψ.1.1 hψ.1.2.1 hΦ).2.comp hc
end GlobalTheory.ThetaTrContF
end

section
abbrev _root_.GlobalTheory.T.doubled_lagrangian_equivariant :=
  GlobalTheory.ThetaTrContF.continuous_thetaTrF_k
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
namespace GlobalTheory.WeilPairPartnerF
theorem pair_partnerF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F]
  E) (B : Base F E),
    GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (a : UG (cA σ) (incM F JA)) (b : UG (cA σ) (incM F JB)),
          ∃ (g : GAF σ JS) (h : GAF σ JT), mtF σ JT h = a.1.1 ∧ mtF σ JS g = (b⁻¹).1.1ᵀ := by
  intro F E _ _ _ _ _ σ B _ _ nS nT JS JT hS _ ξ₀ hξ₀ _ JA JB ξ hA hB a b
  have hmap : ∀ {m n : Type} (X : Matrix m n (AF F ⊗[F] E)),
      X.map (sigR (AF F) σ) = X.map
        (cA σ) :=
    fun X => Matrix.ext fun i j => rfl
  have ha : (a.1.val)ᵀ * incM F JA * (a.1.val).map (cA σ) =
    incM F JA := a.2
  set A : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E) := a.1.val with hAdef
  have hJA : incM F JA = (incM F JT)ᵀ := by
    rw [hA]; rfl
  rw [hJA] at ha
  have ha' := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'
  have hmemA : a.1 ∈ HR (AF F) σ JT := by
    show Formalism.UG.cT _ a.1.val * _ * a.1.val = _
    simp only [Formalism.UG.cT, hmap]
    rw [Matrix.mul_assoc]
    exact ha'
  obtain ⟨cR, hcR⟩ : ∃ f, sigR (AF F) σ = f := ⟨_, rfl⟩
  have hb : (b.1.val)ᵀ * incM F JB * (b.1.val).map cR = incM F JB := by
    rw [← hcR, hmap]; exact b.2
  have hBB : b.1.val * (b⁻¹).1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).mul_inv
  have hBB' : (b⁻¹).1.val * b.1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).inv_mul
  obtain ⟨Bm, hBdef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), b.1.val = M := ⟨_, rfl⟩
  obtain ⟨Bi, hBidef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), (b⁻¹).1.val = M := ⟨_, rfl⟩
  rw [hBdef] at hb hBB hBB'
  rw [hBidef] at hBB hBB'
  have hdet : JS.det ≠ 0 := hS.2
  have hGN := GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := F) (E := E) (AF F)) JS hdet
  have hNG := GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := F) (E := E) (AF F)) JS hdet
  have hsm : incM F (ξ₀ • JS⁻¹) = inclR (F := F) (AF F) ξ₀ • incM F JS⁻¹ :=
    GlobalTheory.WeilPairPartner.map_smul_eq _ _ _
  have hu : IsUnit (inclR (F := F) (E := E) (AF F) ξ₀) :=
    (isUnit_iff_ne_zero.mpr hξ₀).map _
  have hcore := GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu Bm Bi (incM F JB) (incM F JS)
    (incM F JS⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG
  have hTT : Biᵀ * Bmᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  let gU : GL (Fin nS) (AF F ⊗[F] E) :=
    ⟨Biᵀ, Bmᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩
  have hmemB : gU ∈ HR (AF F) σ JS := by
    show Formalism.UG.cT (sigR (AF F) σ) Biᵀ * incM F JS * Biᵀ
      = incM F JS
    rw [hcR]
    simp only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]
    exact hcore
  refine ⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩
  show Biᵀ = ((b⁻¹).1.val)ᵀ
  rw [hBidef]
end GlobalTheory.WeilPairPartnerF
end

section
abbrev _root_.GlobalTheory.T.doubled_lagrangian_intertwiner :=
  GlobalTheory.WeilPairPartnerF.pair_partnerF_k
end

section
open scoped TensorProduct Matrix Classical ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.ThetaSmoothF

theorem contDiff_thetaTr_realF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ :
  E →ₐ[F] E) (B : Base F E),
    GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (finPartF F E) = 0) → ∀ w,
              ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => thetaTr F co B.ψ Φ (w + L t) :=
              by
  intro F E _ _ _ _ _ σ B0' hgood hψ nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ JA JB ξ0 hJA hJB κ _ co hrat Φ hΦ k L hLc hLf w0
  set ψ := B0'.ψ
  obtain ⟨P, Q, hPQ⟩ := darboux_real_coordsF (F := F) (E := E) nS nT κ co.e k L hLc hLf
  obtain ⟨Λ, hΛ⟩ := psiInf_eq_exp_linearF _ ψ hψ
  have hψ1 : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hΛre : ∀ m, (Λ m).re = 0 := by
    intro m
    have h1 := hψ1 (pairA _ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m) 0)
    have h2 := hΛ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m)
    unfold psiInf at h2
    rw [h2, RingEquiv.apply_symm_apply, Complex.norm_exp] at h1
    exact Real.exp_eq_one_iff _ |>.mp h1
  suffices key : ∀ Φ ∈ schA F κ, ∀ w,
      Summable (fun x : κ → F => co.rho ψ w Φ (fun i => algebraMap F (AF F) (x i))) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => thetaTr F co ψ Φ (w + L t) from
    (key Φ hΦ w0).2
  have rho_add : ∀ w (Φ₁ Φ₂ : (κ → AF F) → ℂ), co.rho ψ w (Φ₁ + Φ₂) = co.rho ψ w Φ₁ + co.rho ψ w Φ₂ := by
    intro w Φ₁ Φ₂; funext x; simp [Darboux.rho, schr, mul_add]
  have rho_smul : ∀ w (c : ℂ) (Φ₁ : (κ → AF F) → ℂ), co.rho ψ w (c • Φ₁) = c • co.rho ψ w Φ₁ := by
    intro w c Φ₁; funext x; simp [Darboux.rho, schr]; ring
  have rho_zero : ∀ w, co.rho ψ w (0 : (κ → AF F) → ℂ) = 0 := by
    intro w; funext x; simp [Darboux.rho, schr]
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    intro w
    obtain ⟨M,
      hM⟩ := GlobalTheory.T.summable_rational_schwartzBruhat_mul_polynomial_decay F κ g hg (fun i => ((co.e w).1 i).2)
    let eM := InfiniteAdeleRing.ringEquiv_mixedSpace F
    let emb : (κ → F) → (κ → AF F) := fun x i => algebraMap F (AF F) (x i)
    let embF : (κ → F) → (κ → FiniteAdeleRing (𝓞 F) F) :=
      fun x i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2
    let p0 : mixedEmbedding.mixedSpace F → AF F := fun m => pairA F (eM.symm m) 0
    let yv : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun x i => mixedEmbedding F (x i)
    let ah : κ → mixedEmbedding.mixedSpace F := fun i => eM ((co.e w).1 i).1
    let bh : κ → mixedEmbedding.mixedSpace F := fun i => eM ((co.e w).2 i).1
    let c2 : mixedEmbedding.mixedSpace F := eM (⅟(2 : AF F)).1
    let B0 : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin k → ℝ) →ₗ[ℝ] ℂ :=
      LinearMap.mk₂ ℝ (fun y t => Λ (∑ i, y i * Q t i))
        (fun y₁ y₂ t => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
        (fun r y t => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul])
        (fun y t₁ t₂ => by simp only [map_add (f := _), Pi.add_apply, mul_add, Finset.sum_add_distrib])
        (fun r y t => by simp only [map_smul, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum])
    let B : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap : ((Fin k → ℝ) →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ B0)
    have hB : ∀ y t, B y t = Λ (∑ i, y i * Q t i) := fun y t => rfl
    let hfun : (Fin k → ℝ) → ℂ := fun t => Λ (c2 * ∑ i, (ah i * Q t i + P t i * bh i + P t i * Q t i))
    have hPi : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => P t i :=
      fun i => ((ContinuousLinearMap.proj i).comp P).contDiff
    have hQi : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => Q t i :=
      fun i => ((ContinuousLinearMap.proj i).comp Q).contDiff
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hfun :=
      Λ.contDiff.comp (contDiff_const.mul (ContDiff.sum fun i _ =>
        ((contDiff_const.mul (hQi i)).add ((hPi i).mul contDiff_const)).add ((hPi i).mul (hQi i))))
    have hre : ∀ y t, (B y t + hfun t).re = 0 := fun y t => by rw [hB, ← map_add (f := _)]; exact hΛre _
    let K : (κ → F) → ℂ := fun x =>
      ψ (emb x ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2)) * g (embF x)
    let G : (κ → F) → (Fin k → ℝ) → ℂ := fun x t => Complex.exp (B (yv x) t + hfun t) * f (yv x + ah + P t)
    let term : (κ → F) → (Fin k → ℝ) → ℂ := fun x t => K x * G x t
    have hid : ∀ x t, co.rho ψ (w + L t) (pureA F f g) (emb x) = term x t := by
      intro x t
      let sP : κ → AF F := fun i => p0 (P t i)
      let sQ : κ → AF F := fun i => p0 (Q t i)
      have he : co.e (w + L t) = ((co.e w).1 + sP, (co.e w).2 + sQ) := by rw [map_add (f := _), hPQ t]; rfl
      have hy : ∀ i, eM (emb x i).1 = yv x i := fun i => by
        simp only [emb, yv, eM]; rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl
      have h1 : (fun i => eM ((emb x + ((co.e w).1 + sP)) i).1) = yv x + ah + P t := funext fun i => by
        change eM ((emb x i).1 + (((co.e w).1 i).1 + eM.symm (P t i))) = _
        rw [map_add (f := _), map_add (f := _), eM.apply_symm_apply, hy i, ← add_assoc]; rfl
      have h2 : (fun i => ((emb x + ((co.e w).1 + sP)) i).2) = embF x := funext fun i => by
        change (emb x i).2 + (((co.e w).1 i).2 + 0) = _; rw [add_zero]; rfl
      have hL : co.rho ψ (w + L t) (pureA F f g) (emb x) =
          ψ (emb x ⬝ᵥ ((co.e w).2 + sQ) + ⅟2 * (((co.e w).1 + sP) ⬝ᵥ ((co.e w).2 + sQ))) *
          (f (yv x + ah + P t) * g (embF x)) := by
        rw [← h1, ← h2]; show schr ψ (co.e (w + L t)) _ _ = _; rw [he]; rfl
      rw [hL]
      let φ : AF F →+* mixedEmbedding.mixedSpace F := eM.toRingHom.comp (fstA F).toRingHom
      let φf : AF F →+* FiniteAdeleRing (𝓞 F) F := (sndA F).toRingHom
      have hφp : ∀ n, φ (p0 n) = n := fun n => eM.apply_symm_apply n
      have hφfp : ∀ n, φf (p0 n) = 0 := fun _ => rfl
      set X := emb x ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2) with hX
      set m := ∑ i, yv x i * Q t i + c2 * ∑ i, (ah i * Q t i + P t i * bh i + P t i * Q t i) with hm
      have hsplit : emb x ⬝ᵥ ((co.e w).2 + sQ) + ⅟2 * (((co.e w).1 + sP) ⬝ᵥ ((co.e w).2 + sQ)) = X + p0 m := by
        set Y := emb x ⬝ᵥ sQ + ⅟2 * ((co.e w).1 ⬝ᵥ sQ + sP ⬝ᵥ (co.e w).2 + sP ⬝ᵥ sQ) with hYdef
        have hY : Y = p0 m := by
          refine Prod.ext ?_ ?_
          · apply eM.injective
            change φ Y = φ (p0 m)
            rw [hφp, hm, hYdef]
            have hφx : ∀ i, φ (emb x i) = yv x i := hy
            have hφa : ∀ i, φ ((co.e w).1 i) = ah i := fun _ => rfl
            have hφb : ∀ i, φ ((co.e w).2 i) = bh i := fun _ => rfl
            have hφ2 : φ ⅟2 = c2 := rfl
            simp only [dotProduct, sP, sQ, map_add (f := _), map_mul, map_sum, hφx, hφp, hφa, hφb, hφ2,
              Finset.sum_add_distrib]
          · change φf Y = φf (p0 m)
            rw [hφfp, hYdef]
            simp only [dotProduct, sP, sQ, map_add (f := _), map_mul, map_sum, hφfp, mul_zero, zero_mul,
              Finset.sum_const_zero, add_zero]
        rw [← hY, hYdef, hX]; simp only [dotProduct_add, add_dotProduct]; ring
      have hψY : ψ (p0 m) = Complex.exp (B (yv x) t + hfun t) := by
        change psiInf F ψ (eM.symm m) = _
        rw [hΛ, show InfiniteAdeleRing.ringEquiv_mixedSpace F = eM from rfl, eM.apply_symm_apply, hm, map_add]; rfl
      rw [hsplit, AddChar.map_add_eq_mul, hψY]; simp only [term, K, G]; ring
    have hK : ∀ x, ‖K x‖ = ‖g (embF x)‖ := fun x => by simp only [K, norm_mul, hψ1, one_mul]
    have hG : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G x) := fun x =>
      (Complex.contDiff_exp.comp ((B (yv x)).contDiff.add hsm)).mul
        ((f.smooth ⊤).comp (contDiff_const.add P.contDiff))
    have hsmooth : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (term x) := fun x => contDiff_const.mul (hG x)
    have hbd : ∀ (n : ℕ) (R : ℝ), ∃ u : (κ → F) → ℝ, Summable u ∧
        ∀ x t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (term x) t‖ ≤ u x := by
      intro n R
      obtain ⟨C, hC⟩ := GlobalTheory.ThetaSmooth.norm_iteratedFDeriv_exp_mul_schwartz_le f B hfun hsm hre ah P n M R
      refine ⟨fun x => C * (‖g (embF x)‖ * ((1 + ‖yv x + 0‖) ^ M)⁻¹), (hM 0).mul_left C, fun x t ht => ?_⟩
      have e : term x = K x • G x := rfl
      rw [e, iteratedFDeriv_const_smul_apply ((hG x).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul, hK]
      calc _ ≤ ‖g (embF x)‖ * (C * ((1 + ‖yv x‖) ^ M)⁻¹) := mul_le_mul_of_nonneg_left (hC (yv x) t ht) (norm_nonneg _)
        _ = _ := by simp only [add_zero]; ring
    refine ⟨?_, ?_⟩
    · obtain ⟨u, hu, hu'⟩ := hbd 0 0
      refine Summable.of_norm_bounded hu fun x => ?_
      have h1 := hu' x 0 (by simp)
      rw [norm_iteratedFDeriv_zero, ← hid x 0] at h1
      simpa using h1
    · have e : (fun t => thetaTr F co ψ (pureA F f g) (w + L t)) =
          fun t => ∑' x, term x t := funext fun t => tsum_congr fun x => hid x t
      rw [e]
      exact _root_.GlobalTheory.contDiff_tsum_of_locally_summable_bounds term hsmooth hbd
  | zero =>
    intro w
    simp only [thetaTr, rho_zero, Pi.zero_apply]
    exact ⟨summable_zero, by simpa [thetaSum] using contDiff_const⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    intro w
    refine ⟨by rw [rho_add]; exact (h1 w).1.add (h2 w).1, ?_⟩
    have e : (fun t => thetaTr F co ψ (Φ₁ + Φ₂) (w + L t)) =
        fun t => thetaTr F co ψ Φ₁ (w + L t) +
          thetaTr F co ψ Φ₂ (w + L t) := by
      funext t
      simp only [thetaTr, thetaSum, rho_add, Pi.add_apply]
      exact (h1 (w + L t)).1.tsum_add (h2 (w + L t)).1
    rw [e]; exact (h1 w).2.add (h2 w).2
  | smul c Φ₁ _ h1 =>
    intro w
    refine ⟨by rw [rho_smul]; exact (h1 w).1.const_smul c, ?_⟩
    have e : (fun t => thetaTr F co ψ (c • Φ₁) (w + L t)) =
        fun t => c * thetaTr F co ψ Φ₁ (w + L t) := by
      funext t
      simp only [thetaTr, thetaSum, rho_smul, Pi.smul_apply,
        smul_eq_mul]
      exact tsum_mul_left
    rw [e]; exact contDiff_const.mul (h1 w).2
end GlobalTheory.ThetaSmoothF
end
end

section
abbrev _root_.GlobalTheory.T.doubled_lagrangian_invariant_functional :=
  GlobalTheory.ThetaSmoothF.contDiff_thetaTr_realF_k
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.RatDarbouxTransferF
open scoped Pointwise

theorem haar_fundDomain_transfer_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ
  : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
            IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
            ∃ (ν' : @Measure ((κ → AF F) × (κ → AF F)) (borel _)) (𝓕' : Set ((κ → AF F) × (κ → AF F))),
              @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
              @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F κ) _ _ _ (borel _) 𝓕' ν' ∧
              ∀ f : (κ → AF F) × (κ → AF F) → ℂ,
                ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' := by
  intro F E _ _ _ _ _ σ B _ _ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ _ _ κ _ co hrat ν 𝓕 hν h𝓕
  obtain ⟨hfr, hfin, -⟩ := finrank_AEF F E
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hMT : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  let mP : MeasurableSpace ((κ → AF F) × (κ → AF F)) := borel _
  have : BorelSpace ((κ → AF F) × (κ → AF F)) := ⟨rfl⟩
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  let ce : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E) ≃L[AF F] (κ → AF F) × (κ → AF F) :=
    { co.e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap }
  let ca : WOF F E nS nT ≃ₜ+ (κ → AF F) × (κ → AF F) :=
    { co.e.toAddEquiv with
      continuous_toFun := ce.continuous
      continuous_invFun := ce.symm.continuous }
  let me := ca.toHomeomorph.toMeasurableEquiv
  have into : ∀ g ∈ ratLF F E nS nT, co.e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair F κ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' :=
    onto F E nS nT κ co.e hrat
  refine ⟨ν.map me, me '' 𝓕, ?_, ?_, ?_⟩
  · exact ca.isAddHaarMeasure_map ν
  · refine ⟨?_, ?_, ?_⟩
    · have hqmp : QuasiMeasurePreserving me.symm (ν.map me) ν :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕 = me.symm ⁻¹' 𝓕 :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨co.e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show co.e ((g : WOF F E nS nT) + x) = co.e g + co.e x
      rw [map_add (f := _)]
    · intro p q hpq
      let g : ratLF F E nS nT := ⟨co.e.symm p, onto' p p.2⟩
      let h : ratLF F E nS nT := ⟨co.e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro e
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratLF F E nS nT => co.e (t : WOF F E nS nT)) e
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair F κ) (k : ratLF F E nS nT),
          (k : WOF F E nS nT) = co.e.symm r → r +ᵥ me '' 𝓕 = me '' (k +ᵥ 𝓕) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : (κ → AF F) × (κ → AF F)) + co.e w = co.e ((k : WOF F E nS nT) + w)
        rw [map_add (f := _), hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (ν.map me) (p +ᵥ me '' 𝓕) (q +ᵥ me '' 𝓕)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕.aedisjoint hgh
  · intro f
    rw [MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, lintegral_map_equiv]
    rfl
end GlobalTheory.RatDarbouxTransferF
end
end

section
abbrev _root_.GlobalTheory.T.doubled_lagrangian_theta_compatible :=
  GlobalTheory.RatDarbouxTransferF.haar_fundDomain_transfer_k
end

section
abbrev _root_.GlobalTheory.T.doubled_theta_lift_identity :=
  GlobalTheory.ThetaQuasiRatCM.thetaTr_ratWF_add_quasi_k
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.ThetaTrContCM
theorem continuous_thetaTr_cm_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ :
  E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          Continuous (thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hs hψ JA JB ξ hA hBm κ _ co hco φ hφ
  exact GlobalTheory.ThetaTrContF.continuous_thetaTrF_k F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hs JA JB ξ hA hBm κ
    co hco φ hφ
end GlobalTheory.ThetaTrContCM
end

section
abbrev _root_.GlobalTheory.T.doubled_theta_lift_automorphy :=
  GlobalTheory.ThetaTrContCM.continuous_thetaTr_cm_k
end

section
open scoped TensorProduct Matrix ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.ThetaSmoothCM
theorem contDiff_thetaTr_real_CM_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ
  : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
            ∀ w, ContDiff ℝ ∞ fun t => thetaTr F co B.ψ φ (w + L t) := by
  intro F E _ _ _ _ _ σ B hgood nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ hψ JA JB ξ hJA hJB κ _ co hrat φ hφ k L hLc hLf w
  exact GlobalTheory.T.doubled_lagrangian_invariant_functional F E σ B hgood hψ nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ JA
    JB ξ hJA hJB κ co hrat φ hφ k L hLc hLf w
end GlobalTheory.ThetaSmoothCM
end

section
abbrev _root_.GlobalTheory.T.doubled_theta_lift_nonvanishing :=
  GlobalTheory.ThetaSmoothCM.contDiff_thetaTr_real_CM_k
end

noncomputable section
namespace GlobalTheory.WeilUnitaryTransportF
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
theorem isUnitaryOn_transportF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ :
  E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), IsHeckeCharF χS →
        IsHeckeCharF χT →
        ResEtaF χS nS → ResEtaF χT nT →
        ∀ ω : GAF σ JS × GAF σ JT →* Module.End ℂ
          (WOF F E nS nT → ℂ),
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ χS χT hcS hcT rS rT ω hω JA JB ξ hA hBm κ _ co hrat om hom
  have hψ := hω.std
  rintro μ hμ ⟨a, b⟩ Φ hΦ
  obtain ⟨g, h, hh, hg⟩ := GlobalTheory.T.doubled_lagrangian_intertwiner F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ
    JA JB ξ hA hBm a b
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := _root_.GlobalTheory.TowerFD.exists_fd_any F E nS nT
  obtain ⟨ν', 𝓕', hν', h𝓕', heq⟩ :=
    GlobalTheory.T.doubled_lagrangian_theta_compatible F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ
      co hrat ν 𝓕 hν h𝓕
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_lintegral_sq_eq_mul_setLIntegral_thetaTransform F B.ψ hψ.1 κ μ hμ ν' hν' 𝓕'
    h𝓕'
  have hiso : ∀ Ψ ∈ schA F κ, ∫⁻ x, ‖Ψ x‖ₑ ^ 2 ∂μ =
      c * ∫⁻ w in 𝓕, ‖thetaTr F co B.ψ Ψ w‖ₑ ^ 2 ∂ν := by
    intro Ψ hΨ
    rw [hc Ψ hΨ, ← heq]
    rfl
  have hth : IsThetaFunOF σ JS JT ξ₀ B.ψ (thetaTr F co B.ψ Φ) :=
    ⟨GlobalTheory.T.doubled_lagrangian_continuous F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co
      hrat Φ hΦ,
     GlobalTheory.T.doubled_lagrangian_unitary F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co hrat
       Φ hΦ,
     GlobalTheory.T.doubled_lagrangian_equivariant F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA hBm κ co
       hrat Φ hΦ,
     GlobalTheory.T.doubled_lagrangian_invariant_functional F E σ B hB hψ nS nT JS JT hS hT ξ₀ h0 hσ JA JB ξ hA
       hBm κ co hrat Φ hΦ⟩
  have ht := hom a b g h hh hg Φ hΦ
  calc
    _ = c * ∫⁻ w in 𝓕, ‖thetaTr F co B.ψ ((om (a, b)) Φ) w‖ₑ ^ 2 ∂ν := hiso _ ht.1
    _ = c * ∫⁻ w in 𝓕, ‖thetaTr F co B.ψ Φ w‖ₑ ^ 2 ∂ν := (congrArg (fun f => c * ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂ν) ht.2).trans
        (congrArg (c * ·) (hω.om_unit ν 𝓕 hν h𝓕 _ _ hth))
    _ = _ := (hiso _ hΦ).symm
end GlobalTheory.WeilUnitaryTransportF
end

section
abbrev GlobalTheory.T.weil_representation_pair_unitary :=
  GlobalTheory.WeilUnitaryTransportF.isUnitaryOn_transportF_k
end

noncomputable section
namespace GlobalTheory.TransportHeisF
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem isThetaFunOF_thetaTr_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ φ ∈ schA F κ,
          IsThetaFunOF σ JS JT ξ₀ B.ψ (thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ hA hBξ κ _ co hco φ hφ
  exact
    { quasi := GlobalTheory.T.doubled_theta_lift_identity F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ hA
        hBξ κ co hco φ hφ
      level := GlobalTheory.T.doubled_theta_lift_convergence F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ
        hA hBξ κ co hco φ hφ
      cont := GlobalTheory.T.doubled_theta_lift_automorphy F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB ξ
        hA hBξ κ co hco φ hφ
      smooth := GlobalTheory.T.doubled_theta_lift_nonvanishing F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hstd JA JB
        ξ hA hBξ κ co hco φ hφ }

theorem pres_impl_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), IsHeckeCharF χS →
        IsHeckeCharF χT →
        ResEtaF χS nS → ResEtaF χT nT →
        ∀ ω : GAF σ JS × GAF σ JT →* Module.End ℂ
          (WOF F E nS nT → ℂ),
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) ∧
              ∀ p w, ∀ φ ∈ schA F κ, om p (co.rho B.ψ w φ) = co.rho B.ψ (actAB (cA σ) p w) (om p φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc χS χT hχS hχT rS rT ω hω JA JB ξ hA hBξ κ _ co hco om htr
  have hstd : IsStd B.ψ := hB.std
  have hchar : IsCharAF F B.ψ := hω.std.1
  have key : ∀ p : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB), ∃ (g : GAF σ JS)
      (h : GAF σ JT), mtF σ JT h = p.1.1.1 ∧
        mtF σ JS g = (p.2⁻¹).1.1ᵀ :=
    fun p => match_pairF σ JS JT hS.2 ξ₀ hξ₀ JA JB ξ hA hBξ p.1 p.2
  have pres : ∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ := by
    intro p φ hφ
    obtain ⟨g, h, hh, hg⟩ := key p
    exact (htr p.1 p.2 g h hh hg φ hφ).1
  refine ⟨pres, fun p w φ hφ => ?_⟩
  obtain ⟨a, b⟩ := p
  obtain ⟨g, h, hh, hg⟩ := key (a, b)
  have hs := _root_.GlobalTheory.ThetaQuasiRatF.symp_eq_symplOF' (F := F) σ JS JT ξ₀ JA JB ξ hA hBξ
  have hrho : ∀ w', ∀ φ' ∈ schA F κ, co.rho B.ψ w' φ' ∈ schA F κ :=
    fun w' φ' h' => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ φ' h'
  have h1 := htr a b g h hh hg _ (hrho w φ hφ)
  have h2 := htr a b g h hh hg _ hφ
  have hF := isThetaFunOF_thetaTr_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hξc hω.std JA
    JB ξ hA hBξ κ co hco φ hφ
  have E1 := hω.om_heis g h w _ hF
  have E2 := thetaTr_rhoF σ B.ψ hs co w φ
  have E3 := thetaTr_rhoF σ B.ψ hs co (actAB (cA σ) (a, b) w) (om (a, b) φ)
  have E4 := actOF_eq σ a b g h hh hg w
  have E : thetaTr F co B.ψ (om (a, b) (co.rho B.ψ w φ)) =
      thetaTr F co B.ψ (co.rho B.ψ (actAB (cA σ) (a, b) w) (om (a, b) φ)) := by
    refine h1.2.trans ?_
    refine (congrArg (ω (g, h)) E2).trans ?_
    refine E1.trans ?_
    refine Eq.trans ?_ E3.symm
    exact congrArg₂ (heisOF σ JS JT ξ₀ B.ψ) E4 h2.2.symm
  unfold thetaTr Darboux.rho at E
  refine schr_theta_inj B.ψ hchar κ _ h1.1 _ (hrho _ _ h2.1) fun v => ?_
  obtain ⟨v', rfl⟩ := co.e.surjective v
  exact congrFun E v'
end GlobalTheory.TransportHeisF
end

section
namespace GlobalTheory.WeilAdmCMUnit
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem isUnitaryOn_transport_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ :
  E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), IsHeckeCharF χS →
        IsHeckeCharF χT →
        ResEtaF χS nS → ResEtaF χT nT →
        ∀ ω : GAF σ JS × GAF σ JT →* Module.End ℂ
          (WOF F E nS nT → ℂ),
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om :=
  GlobalTheory.T.weil_representation_pair_unitary
end GlobalTheory.WeilAdmCMUnit
end

section
abbrev GlobalTheory.T.weil_pair_local_factor :=
  GlobalTheory.WeilAdmCMUnit.isUnitaryOn_transport_k

abbrev GlobalTheory.T.weil_representation_pair_continuous :=
  GlobalTheory.TransportHeisF.pres_impl_k
end

noncomputable section
open scoped TensorProduct Matrix ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF (GAF)
namespace GlobalTheory.WeilAdmCM
theorem transport_admissible_weil_datum : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle),
        IsHeckeCharF χS → IsHeckeCharF χT →
        ResEtaF χS nS → ResEtaF χT nT →
        ∀ ω : GAF σ JS × GAF σ JT →* Module.End ℂ
          (WOF F E nS nT → ℂ),
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              ∀ p, ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ om p ∈ (adeleClass F).adm κ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA JB ξ hJA hJB κ _ co hco om htr p
    l hl
  have hP :=
    GlobalTheory.T.weil_representation_pair_continuous F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS
      hrT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hU :=
    GlobalTheory.T.weil_pair_local_factor F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA
      JB ξ hJA hJB κ co hco om htr
  refine weilAdmissible_of_heisenberg_unitary B.ψ hB.std κ (co.e.symm.trans ((GlobalTheory.WeilAdm.actLin _ p).trans
    co.e)) (om p) (hP.1 p)
    (fun w φ hφ => ?_) (fun μ hμ φ hφ => hU μ hμ p φ hφ) l hl
  have h := hP.2 p (co.e.symm w) φ hφ
  simp only [Darboux.rho, LinearEquiv.apply_symm_apply] at h
  exact h
end GlobalTheory.WeilAdmCM
end
