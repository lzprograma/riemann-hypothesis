module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceClosedUnderConjReflection
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticTraceFormAlternatingSwap
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousUnitaryDiagonalEmbeddingDoubled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionDoublingThetaTensorCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledTargetBoxProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFinsetAnnLeK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutProdA
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsSplitAt
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SymplOHFNegNeg
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.UnitaryCharEqOneOfTrivialRationalSplitPlace
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilDatumDoubleSpaceActsUnitScalarSeesawCM
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflections
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoSmulZeroOfCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary

/-! # RestrictCoreK: Consolidated global theta-kernel definitions and proofs (RestrictCoreK). -/
@[expose] public section

open GlobalTheory.WeilSchrodinger (thetaTr)
open UpperTheory.TP.W (GoodK)
open scoped TensorProduct Matrix ComplexConjugate
open GlobalTheory.WeilSchrodinger.DblTargetF (dblG)
open GlobalTheory.DblTargetDelta (deltaT)
open scoped TensorProduct Matrix
open Formalism.IndefR.DatumF (GAF WOF mtF IsWeilDatumOF)
open Formalism.IndefR.DatumF (IsHeckeCharF ResEtaF)
open GlobalTheory.WeilSchrodinger.DblTargetF (coDbl dblG)

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.DblTargetThetaF
open GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem main_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E),
      GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ f₁ f₂ : WOF F E nS nT → ℂ,
        IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → IsThetaFunOF σ JS JT ξ₀ B.ψ f₂
          →
        IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ
          (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ f₁ f₂ h₁ h₂
  exact isThetaFunOF_deltaT σ (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).1.2.1 h₁ h₂
end GlobalTheory.DblTargetThetaF
end
end

section
abbrev GlobalTheory.T.theta_doubling_inner_product :=
  GlobalTheory.DblHeis.heisOF_dblG_deltaT_k
end

noncomputable section
namespace GlobalTheory.DblThetaProd
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem thetaTr_coDbl_boxFun_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E) (B : Base F E),
    GoodK σ B → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F =>
      (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JT JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (hA : JA = JTᵀ) (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ,
        thetaTr F (coDbl hA co) B.ψ (boxFun φ₁ φ₂)
          =
          GlobalTheory.DblTargetDelta.deltaT (thetaTr F co B.ψ φ₁)
            (thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  intro F E _ _ _ _ _ σ B hB hstd nS nT JT JA JB ξ hA κ _ co φ₁ _ φ₂ _
  have hψ := hstd.1.2.1
  have hc : ∀ x, starRingEnd ℂ (B.ψ x) = B.ψ (-x) := fun x => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ x)]
  funext w
  rw [GlobalTheory.DblTargetDelta.deltaT_apply]
  have he : (coDbl hA co).e w =
      (Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).1 (co.e (GlobalTheory.DblTargetDelta.botR w)).1,
        Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).2 (-(co.e (GlobalTheory.DblTargetDelta.botR w)).2)) := rfl
  have hn : co.e (-GlobalTheory.DblTargetDelta.botR w) = -(co.e (GlobalTheory.DblTargetDelta.botR w)) := map_neg _ _
  simp only [thetaTr, thetaSum, Darboux.rho, he, hn]
  generalize co.e (GlobalTheory.DblTargetDelta.topR w) = p₁
  generalize co.e (GlobalTheory.DblTargetDelta.botR w) = p₂
  obtain ⟨x₁, y₁⟩ := p₁
  obtain ⟨x₂, y₂⟩ := p₂
  simp only
  set A : (κ → F) → (κ → AdeleRing (𝓞 F) F) := fun b i => algebraMap F (AdeleRing (𝓞 F) F) (b i) with hAdef
  have key : ∀ q : (κ → F) × (κ → F),
      schr B.ψ (Sum.elim x₁ x₂, Sum.elim y₁ (-y₂)) (boxFun φ₁ φ₂)
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm q i)) =
        schr B.ψ (x₁, y₁) φ₁ (A q.1) *
          (B.ψ (-(A q.2 ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A q.2 + x₂)) := by
    rintro ⟨a, b⟩
    have h1 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inl = A a + x₁ := by
      funext i; simp [hAdef]
    have h2 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inr = A b + x₂ := by
      funext i; simp [hAdef]
    simp only [schr, boxFun]
    rw [h1, h2, mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr, hAdef]
    ring
  rw [← (Equiv.sumArrowEquivProdArrow κ κ F).symm.tsum_eq]
  refine (tsum_congr key).trans ?_
  refine (tsum_prod_mul (fun a => schr B.ψ (x₁, y₁) φ₁ (A a))
    (fun b => B.ψ (-(A b ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A b + x₂))).trans ?_
  congr 1
  rw [Complex.conj_tsum]
  conv_rhs => rw [← (Equiv.neg (κ → F)).tsum_eq]
  refine tsum_congr fun b => ?_
  have h3 : (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.neg (κ → F)) b i)) = -A b := by
    funext i; simp [hAdef]
  simp only [schr, h3, map_mul, Complex.conj_conj, hc,
    Prod.fst_neg, Prod.snd_neg]
  simp only [neg_dotProduct, dotProduct_neg, neg_neg, neg_add, sub_eq_add_neg, mul_neg]
end GlobalTheory.DblThetaProd
end

noncomputable section
open scoped TensorProduct Matrix ComplexConjugate Pointwise
open Formalism.IndefR.DatumF MeasureTheory PositivityTheory.ThKW.Dbl NumberField IsDedekindDomain
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open PositivityTheory.ThKW.DblSchur
open GlobalTheory.DblTargetDelta in
theorem PositivityTheory.ThKW.weil_pair_global_character_lift : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
  [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle)
        (ω : GAF σ JS × GAF σ JT →* Module.End ℂ
          (WOF F E nS nT → ℂ)),
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ ωd : GAF σ JS × GAF σ
        (dblG JT) →*
          Module.End ℂ (WOF F E nS (nT + nT) → ℂ),
        IsWeilDatumOF σ JS (dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : GAF σ JT) (hd : GAF σ
        (dblG JT)),
        mtF σ (dblG JT) hd =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (mtF σ JT h) 0 0 1) →
      ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f₁ f₂ : WOF F E nS nT → ℂ,
        IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → IsThetaFunOF σ JS JT ξ₀ B.ψ f₂
          →
        ωd (1, hd) (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) = c • GlobalTheory.DblTargetDelta.deltaT (ω (1,
          h) f₁) f₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ χS χT ω hω ωd hωd h hd e
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).1
  have hinv : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have hT' := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT
  have hth := fun w f hf => GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ w f hf
  obtain ⟨μ, 𝓕, μ₂, 𝓕₂, hμ, h𝓕, hμ₂, h𝓕₂, hprod⟩ := exists_prod_domain F E nS nT
  let T := {f // IsThetaFunOF σ JS JT ξ₀ B.ψ f}
  have hδ : ∀ f₁ f₂ g₁ g₂ : WOF F E nS nT → ℂ, ∫ x in 𝓕₂, deltaT f₁ f₂ x * star (deltaT g₁ g₂ x) ∂μ₂ =
      (∫ x in 𝓕, f₁ x * star (g₁ x) ∂μ) * ∫ x in 𝓕, conj (f₂ (-x)) * star (conj (g₂ (-x))) ∂μ := fun f₁ f₂ g₁ g₂ => by
    rw [← hprod]
    congr 1; funext x
    simp only [deltaT_apply, star_mul]
    ring
  obtain ⟨c, hc, H⟩ := abstract hψ (_root_.GlobalTheory.SymplSkew.symplOF_swap F E σ hinv _ _ JS _ hS hT'
    ξ₀ hσξ)
    (GlobalTheory.T.rational_lattice_self_dual F E σ B hB _ _ JS _ hS hT' ξ₀ hξ)
    (fun p : T × T => ωd (1, hd) (deltaT p.1.1 p.2.1)) (fun p => deltaT (ω (1, h) p.1.1) p.2.1)
    (fun p => hωd.om_pres _ _ (theta_delta hψ.2.1 p.1.2 p.2.2))
    (fun p => theta_delta hψ.2.1 (hω.om_pres _ _ p.1.2) p.2.2)
    (fun w p => by
      have e1 : actOF σ JS JT 1 h (actOF σ JS JT 1 h⁻¹ (topR w)) = topR w := by
        rw [← GlobalTheory.WeilPartsF.actOF_mul, mul_one, mul_inv_cancel, act_one_left, show mtF σ JT 1 = 1 from rfl,
          Matrix.one_mul]
      have e2 : actOF σ JS _ 1 hd (glue (actOF σ JS JT 1 h⁻¹ (topR w)) (botR w)) = w := by
        rw [act_glue h hd e, e1]
        exact tb_ext (top_glue _ _) (bot_glue _ _)
      refine ⟨(⟨_, hth (actOF σ JS JT 1 h⁻¹ (topR w)) _ p.1.2⟩, ⟨_, hth (-botR w) _ p.2.2⟩), ?_, ?_⟩
      · have := hωd.om_heis 1 hd (glue (actOF σ JS JT 1 h⁻¹ (topR w)) (botR w)) _ (theta_delta hψ.2.1 p.1.2 p.2.2)
        rw [e2, heis_delta hψ.2.1, top_glue, bot_glue] at this
        exact this.symm
      · have := hω.om_heis 1 h (actOF σ JS JT 1 h⁻¹ (topR w)) _ p.1.2
        rw [e1] at this
        show _ = deltaT (ω (1, h) _) _
        rw [this, heis_delta hψ.2.1])
    μ₂ 𝓕₂ hμ₂ h𝓕₂ (fun p q => by
      rw [GlobalTheory.ThetaSchurF.scalar_eq hψ.2.1 μ₂ 𝓕₂ hμ₂ h𝓕₂ (ωd (1, hd)) (hωd.om_pres _) (hωd.om_unit μ₂ 𝓕₂ hμ₂
        h𝓕₂ _) _ _
        (theta_delta hψ.2.1 p.1.2 p.2.2) (theta_delta hψ.2.1 q.1.2 q.2.2), hδ, hδ,
        GlobalTheory.ThetaSchurF.scalar_eq hψ.2.1 μ 𝓕 hμ h𝓕 (ω (1, h)) (hω.om_pres _) (hω.om_unit μ 𝓕 hμ h𝓕 _) _ _ p.1.2
          q.1.2])
  exact ⟨c, hc, fun f₁ f₂ h₁ h₂ => H (⟨f₁, h₁⟩, ⟨f₂, h₂⟩)⟩
end

section
open Formalism.IndefR.DatumF MeasureTheory PositivityTheory.ThKW.Dbl
abbrev GlobalTheory.T.weil_pair_global_character :=
  PositivityTheory.ThKW.weil_pair_global_character_lift
end

section
abbrev GlobalTheory.T.theta_inner_product_formula :=
  GlobalTheory.DblTargetThetaF.main_k
end

section
set_option linter.unusedSectionVars false
noncomputable section
open PositivityTheory.ThKW.SplitChar Filter Topology GlobalTheory.UnRep
open GlobalTheory.SplitCharTrivial (cut cutH cut_val cT_add cT_smul rf tendsto_UJ tendsto_rf norm_cut cut_rf
  exists_seq map_sub_one map_cut)
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF

theorem PositivityTheory.ThKW.unitary_character_trivial_global : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ ν : GAF σ J →* Circle, Continuous ν → (∀ γ ∈ GQF σ J, ν γ = 1) →
        (∀ e, IsSplitIdemF σ e → ∀ g, SuppAtF σ e J g → ν g = 1) → ∀ g,
          ν g = 1 := by
  intro F E _ _ _ _ _ σ B hB n J hJ
  have hcm := hB.cm
  have hσ := GlobalTheory.SplitDetCharF.sig_invol hcm
  obtain ⟨c, rfl⟩ : ∃ c : E ≃ₐ[F] E, (c : E →ₐ[F] E) = σ :=
    ⟨AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ), rfl⟩
  let cs : E →ₐ[F] E := c
  intro ν hν hq hs
  have hH := isHermForm hcm hJ
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split F E cs n J
  have he1 : ∀ g, (mtF _ J g).map (infPartF F E) = (HA.mat _ _ J (e g).1).1 := fun g => (he g).2.symm
  have he2 : ∀ g, (mtF _ J g).map (finPartF F E) = (HA.mat _ _ J (e g).2).1 := fun g => (he g).1.symm
  have hc1 : Continuous fun x : HA (Ainf F) cs J => ν (e.symm (x, 1)) :=
    hν.comp (e.symm.continuous.comp (continuous_id.prodMk continuous_const))
  have hc2 : Continuous fun x : HA (Af F) cs J => ν (e.symm (1, x)) :=
    hν.comp (e.symm.continuous.comp (continuous_const.prodMk continuous_id))
  have hinf : ∀ x, ν (e.symm (x, 1)) = 1 := by
    have hd := GlobalTheory.RealApprox.dense_inf F E cs hσ (GlobalTheory.SplitDetCharF.sig_ne hcm) J
      (Matrix.ext fun i j => hJ.1 i j) hJ.2
    refine fun x => hd.induction (P := fun x => ν (e.symm (x, 1)) = 1) ?_ (isClosed_eq hc1 continuous_const) x
    rintro x ⟨γ, hγ, hx⟩
    obtain ⟨l, hl, e'⟩ := isUnE_eq_prod_refl _ _ c n Jᵀ hH γ.1 ((isUnE_iff γ).2 hγ)
    have h3 := eq_one_rat hcm hH hν hq hs l hl (ratPt γ hγ) (by rw [← e']; rfl)
    have h4 : e.symm (x, 1) = pInf _ J (ratPt γ hγ) := by
      refine ga_ext ?_ ?_
      · rw [he1, e.apply_symm_apply, inf_pInf, mt_ratPt]
        refine (congrArg Units.val hx).symm.trans ?_
        ext i j
        exact (Algebra.TensorProduct.map_tmul _ _ _ _ |>.trans (by rw [map_one]; rfl)).symm
      · rw [he2, e.apply_symm_apply, fin_pInf]; rfl
    rw [h4, h3]
  have hsplit : ∀ g, ν g = ν (e.symm (1, (e g).2)) := fun g => by
    have : g = e.symm ((e g).1, 1) * e.symm (1, (e g).2) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta, e.symm_apply_apply]
    conv_lhs => rw [this, map_mul, hinf, one_mul]
  let μ : HA (Af F) cs J →* Circle := ν.comp (e.symm.toMonoidHom.comp (MonoidHom.inr _ _))
  have hμ : ∀ x, μ x = ν (e.symm (1, x)) := fun _ => rfl
  intro g
  rw [hsplit, ← hμ]
  generalize (e g).2 = x
  let L : Submodule (𝓞 E) (Fin n → E) := Submodule.span (𝓞 E) (Set.range (Pi.basisFun E (Fin n)))
  have hfg : L.FG := Submodule.fg_span (Set.finite_range _)
  have hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤ := by
    rw [Submodule.span_span_of_tower, (Pi.basisFun E (Fin n)).span_eq]
  choose γ h k u1 u2 u3 hg hsup hk hk' using fun N : ℕ =>
    _root_.GlobalTheory.UnRep.exists_rep_suppSplit F E c n Jᵀ hH hcm.2.2.1 L hfg hsp
    (HA.mat _ _ J x) N.factorial ((isUnA_iff _).2 (show HR (Af F) cs J from x).2) N.factorial_pos
  let k' : ℕ → HA (Af F) cs J := fun N => (⟨k N, (isUnA_iff _).1 (u3 N)⟩ : HR (Af F) cs J)
  have h1 : ∀ N, μ x = μ (k' N) := fun N => by
    let h' : HA (Af F) cs J := (⟨h N, (isUnA_iff _).1 (u2 N)⟩ : HR (Af F) cs J)
    let r := ratPt (γ N) ((isUnE_iff _).1 (u1 N))
    have ex : x = (e r).2 * h' * k' N := by
      refine Subtype.ext (Units.ext ((hg N).trans ?_))
      change _ = (HA.mat _ _ J (e r).2).1 * (h N).1 * (k N).1
      rw [← he2, mt_ratPt]; congr 2
    have a1 : μ (e r).2 = 1 := by rw [hμ, ← hsplit]; exact hq _ (ratPt_mem _ _)
    have a2 : μ h' = 1 := by
      obtain ⟨ε, b1, b2, b3, b4⟩ := hsup N
      refine eq_one_of_idem hcm hs ε b1 b2 (fun v hv => (b3 v hv).1) (e.symm (1, h')) ?_
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul]
      refine parts_inj _ _ ?_ ?_
      · have h6 : (mtF _ J (e.symm (1, h'))).map (infPartF F E) = 1 := by rw [he1, e.apply_symm_apply]; rfl
        rw [RingHom.map_mul, map_sub_one, h6, sub_self, Matrix.zero_apply, mul_zero]
      · have h6 : (mtF _ J (e.symm (1, h'))).map (finPartF F E) = (h N).1 := by rw [he2, e.apply_symm_apply]; rfl
        rw [RingHom.map_mul, map_sub_one, h6]; exact congrFun (congrFun b4 i) j
    rw [ex, map_mul, map_mul, a1, a2, one_mul, one_mul]
  have t1 := GlobalTheory.SplitRepsOpen.tendsto_one_of_cong F E L hfg hsp (fun N => (k N).1) hk
  have t2 := GlobalTheory.SplitRepsOpen.tendsto_one_of_cong F E L hfg hsp (fun N => ((k N)⁻¹).1) fun N z hz => by
    obtain ⟨y, hy, e'⟩ := hk N _ (hk' N z hz)
    refine ⟨-y, neg_mem hy, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at e'
    rw [neg_nsmul, ← e', neg_sub]
  have t3 : Tendsto k' atTop (𝓝 1) := tendsto_UJ (sigR (Af F) cs) (JR (Af F) J) t1 t2
  have t := (hc2.tendsto _).comp t3
  have h0 : ν (e.symm (1, 1)) = 1 := by rw [← hμ, map_one]
  rw [h0] at t
  exact tendsto_nhds_unique (tendsto_const_nhds.congr h1) t
end
end

section
abbrev _root_.GlobalTheory.T.unitary_character_trivial_of_local :=
  PositivityTheory.ThKW.unitary_character_trivial_global
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DblTargetRestrictCore
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF in
theorem restrict_core_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F]
  E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle)
        (ω : GAF σ JS × GAF σ JT →* Module.End ℂ
          (WOF F E nS nT → ℂ)),
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ ωd : GAF σ JS × GAF σ
        (dblG JT) →*
          Module.End ℂ (WOF F E nS (nT + nT) → ℂ),
        IsWeilDatumOF σ JS (dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : GAF σ JT) (hd : GAF σ
        (dblG JT)),
        mtF σ (dblG JT) hd =
          Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (mtF σ JT h) 0 0 1) →
      ∀ f₁ f₂ : WOF F E nS nT → ℂ,
        IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → IsThetaFunOF σ JS JT ξ₀ B.ψ f₂
          →
        ωd (1, hd) (deltaT f₁ f₂) = deltaT (ω (1,
          h) f₁) f₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ χS χT ω hω ωd hωd h hd hhd f₁ f₂ hf₁ hf₂
  obtain ⟨ι, hιc, hιm, hιq, hιs, hιd⟩ := _root_.GlobalTheory.DiagEmbU.exists_diagEmb F E σ nT JT
  have ext : ∀ a b : GAF σ (dblG JT), mtF σ (dblG JT) a = mtF σ (dblG JT) b → a = b := fun a b hab =>
    (HR (AF F) σ (dblG JT)).subtype_injective (Units.ext hab)
  have hdι : hd = ι h := ext _ _ (by rw [hhd, hιm])
  subst hdι
  have hsc := fun h' => GlobalTheory.T.weil_pair_global_character F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ χS χT ω
    hω ωd hωd h' (ι h') (hιm h')
  choose c hc1 hc using hsc
  have hth := GlobalTheory.T.theta_inner_product_formula F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  by_cases h0 : ∃ f₀, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0
  swap
  · push Not at h0
    rw [h0 f₁ hf₁]
    have hz : ∀ g : WOF F E nS nT → ℂ, deltaT (0 : WOF F E nS nT → ℂ) g = 0 := fun g => by
      funext x; simp [deltaT]
    simp only [map_zero, hz]
  obtain ⟨f₀, hf₀, hf₀0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hf₀0
  set fs := heisOF σ JS JT ξ₀ B.ψ y f₀ with hfs
  have hfsθ : IsThetaFunOF σ JS JT ξ₀ B.ψ fs := GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS
    JT ξ₀ y f₀ hf₀
  have hfs0 : fs 0 ≠ 0 := by
    have : symplOHF σ JS JT ξ₀ 0 y = 0 := by simp [symplOHF, symplOF, hOF]
    simp only [hfs, heisOF, this, AddChar.map_zero_eq_one, one_mul, zero_add]
    exact hy
  have top0 : topR (0 : WOF F E nS (nT + nT)) = 0 := by ext i j; rfl
  have bot0 : botR (0 : WOF F E nS (nT + nT)) = 0 := by ext i j; rfl
  have dl0 : ∀ a b : WOF F E nS nT → ℂ, deltaT a b 0 = a 0 * conj (b 0) := fun a b => by
    rw [deltaT_apply, top0, bot0, neg_zero]
  have hfsn : fs 0 * conj (fs 0) ≠ 0 := mul_ne_zero hfs0 ((map_ne_zero _).2 hfs0)
  have omi : ∀ h' : GAF σ JT, ω (1, h') (ω (1, h')⁻¹ fs) = fs := fun h' => by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  have pres := hω.om_pres
  have key : ∀ h' (a : ℂ), ωd (1, ι h') (deltaT (ω (1, h')⁻¹ fs) fs) 0 = a * (fs 0 * conj (fs 0)) → c h' = a := by
    intro h' a ha
    have e := congrFun (hc h' (ω (1, h')⁻¹ fs) fs (pres _ _ hfsθ) hfsθ) 0
    rw [Pi.smul_apply, smul_eq_mul, omi, dl0, ha] at e
    exact (mul_right_cancel₀ hfsn e).symm
  have hone : c 1 = 1 := by
    refine key 1 1 ?_
    have p1 : ((1 : GAF σ JS), (1 : GAF σ JT)) = 1 := rfl
    have p2 : ((1 : GAF σ JS), (1 : GAF σ (dblG JT))) = 1 := rfl
    rw [map_one, p1, p2, inv_one, map_one, map_one, one_apply_eq_self, one_apply_eq_self, dl0, one_mul]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    refine key (a * b) _ ?_
    have e1 : ((1 : GAF σ JS), ι (a * b)) = (1, ι a) * (1, ι b) := by rw [map_mul, Prod.mk_mul_mk, one_mul]
    set g := ω ((1 : GAF σ JS), a * b)⁻¹ fs with hg
    have hgθ : IsThetaFunOF σ JS JT ξ₀ B.ψ g := pres _ _ hfsθ
    have comb : ω (1, a) (ω (1, b) g) = fs := by
      rw [← mul_apply_eq_comp, ← map_mul, Prod.mk_mul_mk, one_mul, hg, omi]
    rw [e1, map_mul, mul_apply_eq_comp, hc b g fs hgθ hfsθ, map_smul,
      hc a (ω (1, b) g) fs (pres _ _ hgθ) hfsθ, comb]
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, dl0]
    ring
  let cc : GAF σ JT →* Circle :=
    { toFun := fun h' => ⟨c h', mem_sphere_zero_iff_norm.2 (hc1 h')⟩
      map_one' := Circle.ext hone
      map_mul' := fun a b => Circle.ext (hmul a b) }
  have hcc : ∀ h', (cc h' : ℂ) = c h' := fun _ => rfl
  have hcont : Continuous cc := by
    refine continuous_induced_rng.2 (continuous_iff_continuousAt.2 fun h₀ => ?_)
    set g₁ := ω (1, h₀)⁻¹ fs
    have hg₁ : IsThetaFunOF σ JS JT ξ₀ B.ψ g₁ := pres _ _ hfsθ
    have hN : Continuous fun h' : GAF σ JT => ωd (1, ι h') (deltaT g₁ fs) 0 :=
      (hωd.om_cont _ (hth _ _ hg₁ hfsθ) 0).comp (continuous_const.prodMk hιc)
    have hD : Continuous fun h' : GAF σ JT => ω (1, h') g₁ 0 * conj (fs 0) :=
      ((hω.om_cont _ hg₁ 0).comp (continuous_const.prodMk continuous_id)).mul continuous_const
    have hD0 : ω (1, h₀) g₁ 0 * conj (fs 0) ≠ 0 := by rw [omi]; exact hfsn
    have hev : ∀ᶠ h' in nhds h₀, ω (1, h') g₁ 0 * conj (fs 0) ≠ 0 := hD.continuousAt.eventually_ne hD0
    refine ((hN.continuousAt).div hD.continuousAt hD0).congr (hev.mono fun h' hh' => ?_)
    show ωd (1, ι h') (deltaT g₁ fs) 0 / (ω (1, h') g₁ 0 * conj (fs 0)) = c h'
    rw [hc h' g₁ fs hg₁ hfsθ, Pi.smul_apply, smul_eq_mul, dl0, mul_div_assoc, div_self hh', mul_one]
  have hrat : ∀ γ ∈ GQF σ JT, cc γ = 1 := by
    intro γ hγ
    apply Circle.ext
    rw [hcc, Circle.coe_one]
    have e1 := hωd.om_aut 1 (Subgroup.one_mem _) (ι γ) (hιq γ hγ) _ (hth _ _ hfsθ hfsθ)
    have e2 := hω.om_aut 1 (Subgroup.one_mem _) γ hγ fs hfsθ
    rw [hc γ fs fs hfsθ hfsθ, Pi.smul_apply, smul_eq_mul, dl0, dl0, e2] at e1
    have := mul_right_cancel₀ hfsn (e1.trans (one_mul _).symm)
    exact this
  have hsplit : ∀ e, IsSplitIdemF σ e → ∀ g, SuppAtF σ e JT g → cc g = 1 := by
    intro e he g hg
    have hee : e * e = e := he.1
    obtain ⟨y, hy⟩ : ∃ y : (AEF F E)ˣ, IsDetAtF σ e JT g y := by
      let d := Matrix.GeneralLinearGroup.det (matHomF σ JT g)
      have hd1 : (mtF σ JT g).det * (d⁻¹ : (AEF F E)ˣ) = 1 := d.mul_inv
      have hd2 : (d⁻¹ : (AEF F E)ˣ) * (mtF σ JT g).det = 1 := d.inv_mul
      refine ⟨⟨e * (mtF σ JT g).det + (1 - e), e * (d⁻¹ : (AEF F E)ˣ) + (1 - e), ?_, ?_⟩, rfl⟩
      · linear_combination ((mtF σ JT g).det * (d⁻¹ : (AEF F E)ˣ) - (mtF σ JT g).det - (d⁻¹ : (AEF F E)ˣ) + 1) * hee
          + e * hd1
      · linear_combination ((mtF σ JT g).det * (d⁻¹ : (AEF F E)ˣ) - (mtF σ JT g).det - (d⁻¹ : (AEF F E)ˣ) + 1) * hee
          + e * hd2
    have m1 : mtF σ JS (1 : GAF σ JS) = 1 := by unfold mtF; rw [map_one]; rfl
    have hx1 : IsDetAtF σ e JS 1 1 := by
      show ((1 : (AEF F E)ˣ) : AEF F E) = e * (mtF σ JS 1).det + (1 - e)
      rw [m1, Matrix.det_one, Units.val_one]; ring
    have hS1 : SuppAtF σ e JS 1 := fun i j => by rw [m1, sub_self]; simp
    obtain ⟨rd, hrd, hrd'⟩ := hωd.om_split e he 1 (ι g) hS1 (hιs e g hg) 1 y hx1 (hιd e g y hy)
    obtain ⟨r, hr, hr'⟩ := hω.om_split e he 1 g hS1 hg 1 y hx1 hy
    obtain ⟨ℓ, hℓ, a, b, ha, hb,
      hℓab⟩ := GlobalTheory.T.exists_split_functional_doubled F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he
    have hheis := GlobalTheory.T.theta_doubling_inner_product F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
    have dadd : ∀ f f' : WOF F E nS nT → ℂ, deltaT (f + f') b = deltaT f b + deltaT f' b := fun f f' => by
      funext x; simp only [deltaT_apply, Pi.add_apply, add_mul]
    have dsmul : ∀ (s : ℂ) (f : WOF F E nS nT → ℂ), deltaT (s • f) b = s • deltaT f b := fun s f => by
      funext x; simp only [deltaT_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    let ℓ₁ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => ℓ (deltaT f b)
        map_add' := fun f f' => by simp only [dadd, map_add (f := _)]
        map_smul' := fun s f => by simp only [dsmul, map_smul, RingHom.id_apply] }
    have hℓ₁ : ∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        ℓ₁ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ₁ f := by
      intro u hu f hf
      let ũ : WOF F E nS (nT + nT) := (Matrix.fromRows u 0).submatrix finSumFinEquiv.symm id
      have ht : topR ũ = u := by
        ext i j
        simp only [ũ, topR, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply,
          Matrix.fromRows_apply_inl, id]
      have hb0 : botR ũ = 0 := by
        ext i j
        simp only [ũ, botR, Matrix.submatrix_apply, Function.comp_apply, Equiv.symm_apply_apply,
          Matrix.fromRows_apply_inr, Matrix.zero_apply, id]
      have hu' : ∀ i j, cAF σ e * ũ i j = ũ i j := by
        intro i j
        obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
        rcases i with i | i <;>
          simp only [ũ, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl,
            Matrix.fromRows_apply_inr, Matrix.zero_apply, mul_zero, id, hu]
      have h0b : heisOF σ JS JT ξ₀ B.ψ 0 b = b := by
        funext x; simp [heisOF, symplOHF, symplOF, hOF]
      show ℓ (deltaT (heisOF σ JS JT ξ₀ B.ψ u f) b) = ℓ (deltaT f b)
      have e3 := hheis ũ f b
      rw [ht, hb0, neg_zero, h0b] at e3
      rw [← e3, hℓ ũ hu' _ (hth f b hf hb)]
    have E1 := hrd' ℓ hℓ _ (hth a b ha hb)
    rw [hc g a b ha hb, map_smul, smul_eq_mul] at E1
    have E2 : ℓ (deltaT (ω (1, g) a) b) = (r : ℂ) * (splitFacOF χS χT 1 y : ℂ) * ℓ (deltaT a b) := hr' ℓ₁ hℓ₁ a ha
    have s1 : (splitFacOF χS χT 1 y : ℂ) = χS y := by simp [splitFacOF]
    have s2 : (splitFacOF χS 1 1 y : ℂ) = χS y := by simp [splitFacOF]
    rw [E2, s1] at E1
    rw [s2] at E1
    have hs : (χS y : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hcr : c g * r = rd :=
      mul_right_cancel₀ (mul_ne_zero hs hℓab) (by linear_combination E1)
    have hcg : c g = ((rd / r : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast hr.ne'), hcr]
    have hn := hc1 g
    rw [hcg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hrd hr)] at hn
    apply Circle.ext
    rw [hcc, Circle.coe_one, hcg, hn, Complex.ofReal_one]
  have hall := GlobalTheory.T.unitary_character_trivial_of_local F E σ B hB nT JT hT cc hcont hrat hsplit h
  rw [hc h f₁ f₂ hf₁ hf₂, ← hcc, hall, Circle.coe_one, one_smul]
end GlobalTheory.DblTargetRestrictCore
end
end

section
abbrev GlobalTheory.T.weil_pair_global_intertwiner :=
  GlobalTheory.DblTargetRestrictCore.restrict_core_k
end

section
abbrev _root_.GlobalTheory.T.lagrangian_darboux_theta_model :=
  GlobalTheory.DblThetaProd.thetaTr_coDbl_boxFun_k
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DblTargetRestrict
theorem restrict_boxFun_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle),
        IsHeckeCharF χS → IsHeckeCharF χT →
        ResEtaF χS nS → ResEtaF χT nT →
      ∀ ω : GAF σ JS × GAF σ JT →* Module.End ℂ
        (WOF F E nS nT → ℂ),
        IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E) (hA : JA = JTᵀ),
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
      ∀ ωd : GAF σ JS × GAF σ
        (dblG JT) →*
          Module.End ℂ (WOF F E nS (nT + nT) → ℂ),
        IsWeilDatumOF σ JS (dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
          Module.End ℂ ((κ ⊕ κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ (coDbl hA co) ωd omp →
      ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (incM F (dblG JT)ᵀ)),
        gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
        ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omp (gd, 1) (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT _ _ _ _ ω hω JA JB ξ hA hB' κ _ co hrat om hom
    ωd hωd omp homp g gd hgd φ₁ hφ₁ φ₂ hφ₂
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hω.std.1
  let h : GAF σ JT := ⟨g.1, GlobalTheory.TransportF.mem_HR_target hA g⟩
  let hd : GAF σ (dblG JT) := ⟨gd.1,
    GlobalTheory.TransportF.mem_HR_target rfl gd⟩
  have hh : mtF σ JT h = g.1.1 := rfl
  have hhd : mtF σ (dblG JT) hd = gd.1.1 := rfl
  have h1 : mtF σ JS 1 = ((1 : UG (cA σ) (incM F JB))⁻¹).1.1ᵀ := by
    show (Formalism.IndefR.DatumF.matHomF σ JS 1).1 = _
    rw [map_one, inv_one]
    simp
  have hdm : mtF σ (dblG JT) hd =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (mtF σ JT h) 0 0 1) := by
    rw [hhd, hgd, hh]
  have t1 := hom g 1 1 h hh h1 φ₁ hφ₁
  have hΦ := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ₁ hφ₁ φ₂ hφ₂
  have hΦ' := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ t1.1 φ₂ hφ₂
  have t2 := homp gd 1 1 hd hhd h1 _ hΦ
  have hφ₂' := _root_.GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection F κ φ₂ hφ₂
  let τ := Fintype.equivFin κ
  have he : ∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' =
      GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF co τ w) (GlobalTheory.TransportF.numCoordF co
        τ w') := fun w w' => by
    rw [GlobalTheory.TransportF.symplOF_eq_symp hA hB', co.form]
    simp only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply,
      comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card κ) → F,
      GlobalTheory.TransportF.numCoordF co τ (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y,
        GlobalTheory.SWQ.rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩
  have thf : ∀ Φ ∈ schA F κ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ
      (thetaTr F co B.ψ Φ) := fun Φ hΦ => by
    rw [GlobalTheory.TransportF.thetaTr_eqF co τ]
    exact GlobalTheory.T.schrodinger_model_isomorphism F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _
      (GlobalTheory.TransportF.numCoordF co τ) he hr _
      (GlobalTheory.TransportF.comp_mem_schA τ hΦ)
  have key := t2.2.trans ((congrArg (ωd (1,
    hd)) (GlobalTheory.T.lagrangian_darboux_theta_model F E σ B hB hω.std nS nT JT JA JB ξ hA κ co φ₁ hφ₁ φ₂
    hφ₂)).trans
    ((GlobalTheory.T.weil_pair_global_intertwiner F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT ω hω ωd hωd h hd
      hdm _ _ (thf φ₁ hφ₁) (thf _ hφ₂')).trans
      ((congrArg (fun f => GlobalTheory.DblTargetDelta.deltaT f
        (thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x))))) t1.2.symm).trans
        (GlobalTheory.T.lagrangian_darboux_theta_model F E σ B hB hω.std nS nT JT JA JB ξ hA κ co _ t1.1 φ₂
          hφ₂).symm)))
  let τ' := Fintype.equivFin (κ ⊕ κ)
  erw [GlobalTheory.TransportF.thetaTr_eqF (ψ := B.ψ) (coDbl hA co) τ' ((omp
    (gd, 1)) (boxFun φ₁ φ₂))] at key
  erw [GlobalTheory.TransportF.thetaTr_eqF (ψ := B.ψ) (coDbl hA co) τ' (boxFun
    (om (g, 1) φ₁) φ₂)] at key
  have h2 := GlobalTheory.TransportF.thV_injOn hR hψ (GlobalTheory.TransportF.comp_mem_schA τ' t2.1)
    (GlobalTheory.TransportF.comp_mem_schA τ' hΦ')
    ((GlobalTheory.TransportF.numCoordF (coDbl hA co)
      τ').surjective.injective_comp_right key)
  funext x
  have hx : (x ∘ τ'.symm) ∘ τ' = x := by
    funext i
    simp
  erw [← hx]
  exact congrFun h2 (x ∘ τ'.symm)
end GlobalTheory.DblTargetRestrict
end
end

section
abbrev _root_.GlobalTheory.T.doubled_weil_apply_boxFun_eq_boxFun_left :=
  GlobalTheory.DblTargetRestrict.restrict_boxFun_k
end
