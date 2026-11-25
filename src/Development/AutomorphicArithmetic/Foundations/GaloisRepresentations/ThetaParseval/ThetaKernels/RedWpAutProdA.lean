module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMRealLineFiniteInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSelfOfTrivial
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalvedSymplecticFormFiniteRealOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpDoubledGramDoublingThetaTensor
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFPreservesIsThetaFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointsSelfAnnihilatorSymplecticStandardC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharHalfSymplecticFormRealCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointEqRealMulFiniteBothOrders
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutDef
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ContinuousTheta
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepC
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SpanInfRatF
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SumFourEqTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator

/-! # RedWpAutProdA: Consolidated global theta-kernel definitions and proofs (RedWpAutProdA). -/
@[expose] public section

open PositivityTheory.ThKW (Ctx_k)
open UpperTheory.TP.W (GoodK IsLatRepL)
open Complex (I exp)
open Real (pi)
open Set (range)
open Submodule (span)

section
open UpperTheory.TP.W (GoodK)
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
  MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealWeil
  GlobalTheory.RealWeilF Classical
namespace GlobalTheory.RealWeilF
theorem actOF_iotaVF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F]
  E)
    (B : Base F E),
      GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (g : GAF σ JS) (h : GAF σ JT) (v : IxF F nS nT → ℂ),
        actOF σ JS JT g h (iotaVF ι v) = iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v) := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ θ _ ι hι g h v
  have hfin : ∀ u : IxF F nS nT → ℂ, (iotaVF ι u).map (finPartF F E) = 0 := fun u => real_iotaVF hι u
  have hL : (actOF σ JS JT g h (iotaVF ι v)).map (finPartF F E) = 0 := by
    unfold actOF
    rw [Matrix.map_mul, Matrix.map_mul, hfin, Matrix.mul_zero, Matrix.zero_mul]
  have hcpt : ∀ (u : IxF F nS nT → ℂ) w, compAtF θ w (iotaVF ι u) = GlobalTheory.RealWeil.cpt u w := by
    intro u w
    ext i j
    exact hι.comp _ w
  have hC : ∀ w, compAtF θ w (actOF σ JS JT g h (iotaVF ι v)) =
      compAtF θ w (iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v)) := by
    intro w
    have e : compAtF θ w (actOF σ JS JT g h (iotaVF ι v)) =
        compAtF θ w (mtF σ JT h) * compAtF θ w (iotaVF ι v) * compAtF θ w (mtF σ JS g⁻¹) := by
      unfold actOF compAtF
      rw [Matrix.map_mul, Matrix.map_mul]
    rw [e, hcpt, hcpt, mMF_apply, GlobalTheory.RealWeil.cpt_blk]
  ext i j
  rw [← sub_eq_zero]
  refine hι.ext _ ?_ fun w => ?_
  · have h1 : finPartF F E (actOF σ JS JT g h (iotaVF ι v) i j) = 0 := congrFun (congrFun hL i) j
    have h2 : finPartF F E (iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v) i j) = 0 := congrFun (congrFun (hfin _) i) j
    rw [RingHom.map_sub, h1, h2, sub_zero]
  · have h3 := congrFun (congrFun (hC w) i) j
    simp only [compAtF, Matrix.map_apply, RingHom.comp_apply] at h3
    rw [RingHom.map_sub, RingHom.map_sub, h3, sub_self]
end GlobalTheory.RealWeilF
end

abbrev _root_.GlobalTheory.T.actOF_iotaVF_eq_iotaVF_mulVec :=
  GlobalTheory.RealWeilF.actOF_iotaVF_k
end

noncomputable section
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF MeasureTheory
  GlobalTheory.FinWeil GlobalTheory.FinLatF
open UpperTheory.TP.W (GoodK)
namespace PositivityTheory.ThKW.LatA
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {nS nT : ℕ}
  {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E} {ψ : AddChar (AF F) ℂ}
theorem sig_sig_k {B : Base F E} (hB : GoodK σ B) (x : E) : σ (σ x) = x := by
  let τ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
variable {hc : HeisClosedF σ JS JT ξ₀ ψ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)}
theorem sys_k (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    (h : IsLatRepL σ JS JT ξ₀ ψ hc Λ w lam Om) :
    GlobalTheory.LatticeRep.IsLatSystem (sgOF σ) w (gamFF σ JS JT ξ₀ ψ) (opFF hc w) lam (latF F E nS nT Λ) (rhoFF σ JS
      JT) :=
  ⟨isHeis_opFF hσ hS hT hξ hc h.hw, h.good, h.sd, h.span, gamFF_rhoFF hS, h.fin⟩
theorem rep_k (h : IsLatRepL σ JS JT ξ₀ ψ hc Λ w lam Om) :
    GlobalTheory.LatticeRep.IsLatRep (opFF hc w) lam (latF F E nS nT Λ) (rhoFF σ JS JT) Om :=
  ⟨h.op, h.vac⟩
theorem eventually_fix_k (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    (h : IsLatRepL σ JS JT ξ₀ ψ hc Λ w lam Om) (f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀
      ψ) :
    ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), Om p f = f := by
  have hs := sys_k hσ hS hT hξ h
  have H := hs.1
  refine GlobalTheory.LatticeRep.transl_induction hs.2.2.2.1 (p := fun f => ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT),
    Om p f = f)
    (fun x e he => ?_) (Filter.Eventually.of_forall fun p => map_zero _) (fun u v hu hv => ?_) (fun c u hu => ?_) f
  · obtain ⟨N, hN, hNU⟩ := h.lev (w • x)
    filter_upwards [h.near, h.near' x N hN] with p hp hp'
    obtain ⟨l, hl, e1⟩ := hp'
    have e2 : gamFF σ JS JT ξ₀ ψ (w • x) (N • l) = 1 := by
      rw [gamFF, ← symplOHF_add_self, AddChar.map_add_eq_mul, XFF.coe_nsmul, hNU l hl, one_mul]
    have e4 := H.comp x (N • l) e
    rw [he _ (nsmul_mem hl N), e2, one_smul] at e4
    rw [h.op, (rep_k h).fix_of_map_le hs (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha) he, e1, ← e4]
  · filter_upwards [hu, hv] with p h3 h4 using by rw [map_add (f := _), h3, h4]
  · filter_upwards [hu] with p h3 using by rw [map_smul, h3]
end PositivityTheory.ThKW.LatA
end

noncomputable section
namespace GlobalTheory.StdCharWeilDatum
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem isStdCharF_of_isGood_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F =>
      (B.emb w).1) B.ψ (-1) := by
  intro F E _ _ _ _ _ σ B hB
  have := hB.cm.1
  refine ⟨isCharAF hB.std, ⟨?_, fun θ hθ x => ?_⟩⟩
  · choose θ hθ using fun w : InfinitePlace F =>
      GlobalTheory.DualPairCompare.gen_inf_exists (B.emb w).1 w (B.emb w).2.symm
    exact ⟨θ, hθ⟩
  · show B.ψ (pairA F x 0) = _
    rw [psi_pairA hB.std, sum_infFam B θ hθ x]
    congr 1
    push_cast
    ring
end GlobalTheory.StdCharWeilDatum
end

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
  MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealWeil
  GlobalTheory.RealWeilF Classical
open UpperTheory.TP.W (GoodK)
noncomputable section
namespace GlobalTheory.RealCharF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem psi_symplOHF_iotaVF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E)
    (B : Base F E),
      GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ u v : IxF F nS nT → ℂ, B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ u).im :
          ℂ)) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ θ hθ ι hι u v
  have hσ := hB.cm
  have : IsTotallyReal F := hσ.1
  have hψ := GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB
  have hw : ∀ w : InfinitePlace F, w.embedding = (B.emb w).1.comp (algebraMap F E) := fun w => (B.emb w).2.symm
  set s := symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v) with hs
  have hsnd : sndA F s = 0 :=
    GlobalTheory.HeisDerivCM.map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ _ _ (Or.inr (real_iotaVF hι v))
  have e1 : B.ψ s = psiInf F B.ψ (fstA F s) := by
    have hsplit : s = pairA F (fstA F s) 0 := Prod.ext rfl hsnd
    conv_lhs => rw [hsplit]
    rfl
  have hre : ∀ w : InfinitePlace F, ((B.emb w).1 ξ₀).re = 0 := by
    intro w
    have h1 := hσ.2.2.2 (B.emb w).1 ξ₀
    rw [hσξ, map_neg] at h1
    have h2 := congrArg Complex.re h1
    rw [Complex.neg_re, Complex.star_def, Complex.conj_re] at h2
    linarith
  rw [e1, hψ.2.2 θ hθ, trace_HMF]
  have e2 : ∑ w, θ w (fstA F s ⊗ₜ[F] (1 : E)) = ∑ w, ((((B.emb w).1 ξ₀) *
      ((JS.map (B.emb w).1)⁻¹ * (cpt v w)ᴴ * JT.map (B.emb w).1 * cpt u w).trace).re : ℂ) :=
    Finset.sum_congr rfl fun w _ => by
      rw [hs, theta_fstA_symplOHF hσ (hw w) (hθ w) JS JT ξ₀ (iotaVF ι u) (iotaVF ι v),
        theta_hOF hσ hw hθ hι JT hJS.2 u v]
  rw [e2]
  congr 1
  rw [Complex.im_sum]
  simp only [Complex.mul_re, hre, Complex.im_ofReal_mul, zero_mul, zero_sub]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring
end GlobalTheory.RealCharF
end
end

section
open UpperTheory.TP.W (GoodK)
abbrev _root_.GlobalTheory.T.archimedean_chart_theta_equivariant :=
  GlobalTheory.RealCharF.psi_symplOHF_iotaVF_k
end

section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.DblTargetDelta (deltaT)
open GlobalTheory.WeilSchrodinger.DblTargetF (dblG)
open UpperTheory.TP.W (GoodK)
noncomputable section
namespace GlobalTheory.DblHeis
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem heisOF_dblG_deltaT_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (w : WOF F E nS (nT + nT)) (f₁ f₂ : WOF F E nS nT → ℂ),
        heisOF σ JS (dblG JT) ξ₀ B.ψ w
          (deltaT f₁ f₂) =
          deltaT (heisOF σ JS JT ξ₀ B.ψ
            (GlobalTheory.DblTargetDelta.topR w) f₁)
            (heisOF σ JS JT ξ₀ B.ψ (-GlobalTheory.DblTargetDelta.botR w) f₂) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ w f₁ f₂
  have hn := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).1.2.1
  funext x
  have ht : topR (x + w) = topR x + topR w := rfl
  have hb : -botR (x + w) = -botR x + -botR w := by
    rw [← neg_add]; rfl
  simp only [heisOF, deltaT_apply, ht, hb, symplOHF_dblG, map_mul, conj_psi hn, sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring
end GlobalTheory.DblHeis
end
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF
open UpperTheory.TP.W (GoodK)
noncomputable section
namespace GlobalTheory.RatAnnihF
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem adele_rat_of_isGood_k {σ : E →ₐ[F] E} {B : Base F E} (hB : GoodK σ B) (a : AF F)
    (h : ∀ c : F, B.ψ (a * algebraMap F _ c) = 1) : ∃ d : F, a = algebraMap F _ d := by
  have := hB.cm.1
  obtain ⟨⟨θ, hθ⟩, -⟩ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).2
  let L : Ainf F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ w, θ w (x ⊗ₜ[F] (1 : E))) fun a b => by
    simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib]
  have hL : ∀ x,
    L x = ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) :=
    fun x => GlobalTheory.StdCharWeilDatum.sum_infFam B θ hθ x
  refine GlobalTheory.RatAnnih.adele_rat (GlobalTheory.StdCharWeilDatum.isCharAF hB.std) (psiV_exists_ne_one hB.std) L
    (continuous_finsetSum _ fun w _ => (hθ w).2) (fun x => ?_) (fun x => ?_) a h
  · rw [hL]
    have e : InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (Ainf F) x) = mixedEmbedding F x := by
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rw [e, GlobalTheory.LatVacArith.trace_mixedEmbedding]
    exact Complex.ofReal_ratCast _
  · show B.ψ (pairA F x 0) = _
    rw [GlobalTheory.StdCharWeilDatum.psi_pairA hB.std, hL]
    congr 1
    ring
end
theorem ratLF_annihilator_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E)
    (B : Base F E),
      GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → ∀ x : WOF F E nS nT,
      (∀ γ ∈ ratLF F E nS nT, B.ψ (symplOF σ JS JT ξ₀ x γ) = 1) ↔ x ∈ ratLF F E nS nT := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ x
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hB.cm.2.2.1]; norm_num)
  have hσ := (Algebra.IsAlgebraic.algHom_bijective σ).2
  constructor
  · intro h
    have hent : ∀ i j, ∃ e : E, x i j = (1 : AF F) ⊗ₜ[F] e := fun i j =>
      GlobalTheory.RatAnnih.tensor_rat (x i j) fun e => adele_rat_of_isGood_k hB _ fun c => by
        obtain ⟨γ, hγ, hγe⟩ := exists_symplOF_eq σ hσ hS hT hξ x i j (c • e)
        exact (congrArg B.ψ ((GlobalTheory.RatAnnih.trace_mul_algebraMap (x i j) e c).trans hγe.symm)).trans (h γ hγ)
    choose M hM using hent
    refine ⟨Matrix.of M, Matrix.ext fun i j => ?_⟩
    rw [hM i j]
    rfl
  · rintro ⟨M, rfl⟩ _ ⟨N, rfl⟩
    obtain ⟨a, ha⟩ := symplOF_rat σ JS JT ξ₀ M N
    rw [ha]
    exact (GlobalTheory.StdCharWeilDatum.isCharAF hB.std).2.2.1 a
end GlobalTheory.RatAnnihF
end
end

section
open UpperTheory.TP.W (GoodK)
abbrev _root_.GlobalTheory.T.rational_lattice_self_dual :=
  GlobalTheory.RatAnnihF.ratLF_annihilator_k
end

section
abbrev _root_.GlobalTheory.T.standard_additive_character_sign :=
  GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k
end

noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF MeasureTheory
  GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
open UpperTheory.TP.W (GoodK)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PositivityTheory.ThKW.TauSpanIdentities
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT)
  E} {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
theorem _root_.PositivityTheory.ThKW.piWF_ratWF_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (y : Matrix (Fin nT) (Fin nS) E) :
    piWF θ (ratWF y) = infRatF (tauB B) y := by
  funext p
  exact RealC.theta_inc (C.inf p.2) _
theorem _root_.PositivityTheory.ThKW.continuous_piWF_k (C : Ctx_k σ B JS JT ξ₀ θ ι) : Continuous (piWF (nS := nS)
  (nT := nT) θ) :=
  continuous_pi fun p => (RealC.continuous_theta (C.inf p.2)).comp
    ((continuous_apply p.1.2).comp (continuous_apply p.1.1))
theorem _root_.PositivityTheory.ThKW.beta_iota_right_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (x : WOF F E nS nT)
  (v : IxF F nS nT → ℂ) :
    B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)) =
      exp (-(pi * I) * (omV (HMF JS JT ξ₀ (tauB B)) (piWF θ x) v : ℝ)) := by
  have hx := finIdem_add_iota C.chart x
  have h0 := (_root_.GlobalTheory.WeilDatumF.symplOHF_fin_real_orth F E σ nS nT JS JT ξ₀ (finIdem F E • x) (iotaVF
    ι v) (finIdem_smul_fin x)
    (real_iotaVF C.chart v)).1
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.symplOHF_add_left, h0, zero_add,
    GlobalTheory.T.archimedean_chart_theta_equivariant F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf
      ι C.chart, omV_apply]
  congr 1
  push_cast
  ring
theorem _root_.PositivityTheory.ThKW.beta_iota_left_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (v : IxF F nS nT → ℂ)
  (x : WOF F E nS nT) :
    B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι v) x) =
      exp (-(pi * I) * (omV (HMF JS JT ξ₀ (tauB B)) v (piWF θ x) : ℝ)) := by
  have hx := finIdem_add_iota C.chart x
  have h0 := (_root_.GlobalTheory.WeilDatumF.symplOHF_fin_real_orth F E σ nS nT JS JT ξ₀ (finIdem F E • x) (iotaVF
    ι v) (finIdem_smul_fin x)
    (real_iotaVF C.chart v)).2
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.symplOHF_add_right, h0, zero_add,
    GlobalTheory.T.archimedean_chart_theta_equivariant F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf
      ι C.chart, omV_apply]
  congr 1
  push_cast
  ring
theorem _root_.PositivityTheory.ThKW.piWF_actOF_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT)
  (x : WOF F E nS nT) :
    piWF θ (actOF σ JS JT g h x) = mMF σ JS JT θ (g, h) *ᵥ piWF θ x := by
  have hx := finIdem_add_iota C.chart x
  conv_lhs => rw [hx]
  rw [GlobalTheory.RealWeilF.actOF_add, piWF_add, piWF_of_fin (actOF_fin g h (finIdem_smul_fin x)), zero_add,
    GlobalTheory.T.actOF_iotaVF_eq_iotaVF_mulVec F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ C.inf ι
      C.chart g h, piWF_iotaVF C.chart]
theorem _root_.PositivityTheory.ThKW.psi_rat_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    B.ψ (symplOHF σ JS JT ξ₀ (ratWF x) (ratWF y)) = 1 := by
  rw [symplOHF_rat]
  exact C.good.std.2.1 _
theorem _root_.PositivityTheory.ThKW.symplOF_actOF_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT)
  (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOF σ JS JT ξ₀ x y := by
  unfold symplOF
  rw [_root_.PositivityTheory.ThKW.LatA.hOF_actOF C.hS]
theorem _root_.PositivityTheory.ThKW.gamQF_eq_one_iff_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E)
  :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔
      ∃ z : ℤ, omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y) = z := by
  have hx : ratWF (F := F) x = finIdem F E • ratWF (F := F) x + iotaVF ι (infRatF (tauB B) x) := by
    have := finIdem_add_iota C.chart (ratWF (F := F) x); rwa [piWF_ratWF_k C] at this
  have hy : ratWF (F := F) y = finIdem F E • ratWF (F := F) y + iotaVF ι (infRatF (tauB B) y) := by
    have := finIdem_add_iota C.chart (ratWF (F := F) y); rwa [piWF_ratWF_k C] at this
  have cross : ∀ (a : WOF F E nS nT) (b : IxF F nS nT → ℂ), a.map (infPartF F E) = 0 →
      symplOHF σ JS JT ξ₀ a (iotaVF ι b) = 0 ∧ symplOHF σ JS JT ξ₀ (iotaVF ι b) a = 0 :=
    fun a b ha => _root_.GlobalTheory.WeilDatumF.symplOHF_fin_real_orth F E σ nS nT JS JT ξ₀ a (iotaVF ι b) ha
      (real_iotaVF C.chart b)
  have hr := psi_rat_k C x y
  rw [hx, hy, GlobalTheory.RealWeilF.symplOHF_add_left, GlobalTheory.RealWeilF.symplOHF_add_right,
    GlobalTheory.RealWeilF.symplOHF_add_right,
    (cross _ _ (finIdem_smul_fin _)).1, (cross _ _ (finIdem_smul_fin _)).2, add_zero, zero_add,
    AddChar.map_add_eq_mul, beta_iota_right_k C, piWF_iotaVF C.chart] at hr
  set om := omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y)
  set P := B.ψ (symplOHF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y))
  have hg : gamQF σ JS JT ξ₀ B.ψ x y = P * P := by
    show B.ψ (symplOF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y)) = _
    rw [symplOF_eq_add, AddChar.map_add_eq_mul]
  have hP : P = Complex.exp (Real.pi * Complex.I * (om : ℂ)) := by
    calc P = P * (Complex.exp (-(Real.pi * Complex.I) * (om : ℂ)) * Complex.exp (Real.pi * Complex.I * (om : ℂ))) := by
          rw [← Complex.exp_add, show -(Real.pi * Complex.I) * (om : ℂ) + Real.pi * Complex.I * (om : ℂ) = 0 by ring,
            Complex.exp_zero, mul_one]
      _ = _ := by rw [← mul_assoc, hr, one_mul]
  rw [hg, hP, ← Complex.exp_add, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : (2 : ℂ) * (Real.pi * Complex.I) ≠ 0 :=
      mul_ne_zero two_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero)
    have : (om : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ hpi
      linear_combination hn
    exact_mod_cast this
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn]; push_cast; ring⟩
theorem sig_sig_k (hB : GoodK σ B) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
theorem _root_.PositivityTheory.ThKW.gamQF_eq_one_iff'_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E)
  :
    gamQF σ JS JT ξ₀ B.ψ x y = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y) = n := by
  have := C.good.cm.1
  have := Module.Finite.of_restrictScalars_finite ℚ F E
  have h1 : gamQF σ JS JT ξ₀ B.ψ x y =
      B.ψ (pairA F 0 (algebraMap F (Af F) (Algebra.trace F E (ξ₀ * hRatF σ JS JT x y)))) := by
    have := LatC.sympl_ft (σ := σ) (JS := JS) (JT := JT) (ξ₀ := ξ₀) (sig_sig_k C.good) 1 1 x y
    rw [one_mul, one_mul] at this
    show B.ψ (symplOF σ JS JT ξ₀ (finIdem F E • ratWF (F := F) x) (finIdem F E • ratWF (F := F) y)) = _
    exact congrArg B.ψ this
  have h2 : ∀ t : F,
    pairA F 0 (algebraMap F (Af F) t) = algebraMap F (AF F) t + pairA F (-(algebraMap F (Ainf F) t)) 0 := by
    intro t
    refine Prod.ext ?_ ?_
    · show (0 : Ainf F) = algebraMap F (Ainf F) t + -(algebraMap F (Ainf F) t)
      rw [add_neg_cancel]
    · show algebraMap F (Af F) t = algebraMap F (Af F) t + 0
      rw [add_zero]
  have h3 : ∀ t : F, B.ψ (pairA F (-(algebraMap F (Ainf F) t)) 0) =
      exp (2 * pi * I * algebraMap ℚ ℂ (Algebra.trace ℚ F t)) := by
    intro t
    have hw : ∀ w, θ w ((-(algebraMap F (Ainf F) t)) ⊗ₜ[F] (1 : E)) = -(w.embedding t) := by
      intro w
      have e : (algebraMap F (Ainf F) t) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] algebraMap F E t := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      rw [TensorProduct.neg_tmul, map_neg, e, (C.inf w).1]
      exact congrArg Neg.neg (RingHom.congr_fun (B.emb w).2 t)
    rw [GlobalTheory.StdCharWeilDatum.psi_pairA C.good.std, ← GlobalTheory.StdCharWeilDatum.sum_infFam B θ C.inf,
      trace_places]
    congr 1
    simp only [hw, Finset.sum_neg_distrib]
    ring
  rw [h1, h2, AddChar.map_add_eq_mul, C.good.std.2.1, one_mul, h3, Complex.exp_eq_one_iff, Algebra.trace_trace]
  have hpi : (2 : ℂ) * pi * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h4 : algebraMap ℚ ℂ (Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT x y)) = (n : ℂ) :=
      mul_left_cancel₀ hpi (by linear_combination hn)
    rw [eq_ratCast (algebraMap ℚ ℂ)] at h4
    exact_mod_cast h4
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn, map_intCast]; ring⟩
section Span
theorem span_tau_k (hB : GoodK σ B) :
    span ℝ (range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) = ⊤ := by
  have := hB.cm.2.1
  have hall : ∀ z ∈ span ℝ (range (mixedEmbedding E)),
      Lm B z ∈ span ℝ (range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨e, rfl⟩ := hz
      apply Submodule.subset_span
      refine ⟨e, ?_⟩
      funext w
      show (B.emb w).1 e = cw B w ((wE B w).embedding e)
      rw [cw_emb]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have htop : span ℝ (range (mixedEmbedding E)) = ⊤ := by
    refine eq_top_iff.2 (le_trans (le_of_eq (mixedEmbedding.latticeBasis E).span_eq.symm) (Submodule.span_mono ?_))
    rintro _ ⟨i, rfl⟩
    exact ⟨_, (mixedEmbedding.latticeBasis_apply E i).symm⟩
  rw [eq_top_iff]
  rintro f -
  let z : mixedEmbedding.mixedSpace E :=
    (0, fun W => cw B (W.1.comap (algebraMap F E)) (f (W.1.comap (algebraMap F E))))
  have hz : Lm B z = f := by
    funext w
    show cw B w (cw B ((wE B w).comap (algebraMap F E)) (f ((wE B w).comap (algebraMap F E)))) = f w
    rw [wE_comap, cw_cw]
  rw [← hz]
  exact hall z (htop ▸ Submodule.mem_top)
theorem _root_.PositivityTheory.ThKW.span_infRatF_k (hB : GoodK σ B) :
    Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B))) = ⊤ := by
  set V := Submodule.span ℝ (Set.range (infRatF (nS := nS) (nT := nT) (tauB B)))
  have key : ∀ (q : Fin nT × Fin nS) (g : InfinitePlace F → ℂ),
      (fun p : IxF F nS nT => if p.1 = q then g p.2 else 0) ∈ V := by
    intro q g
    have hg : g ∈ Submodule.span ℝ (Set.range fun e : E => fun w : InfinitePlace F => (B.emb w).1 e) := by
      rw [span_tau_k hB]; trivial
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨e, rfl⟩ := hg
      apply Submodule.subset_span
      refine ⟨Matrix.of fun a b => if (a, b) = q then e else 0, ?_⟩
      funext p
      show (B.emb p.2).1 (if (p.1.1, p.1.2) = q then e else 0) = if p.1 = q then (B.emb p.2).1 e else 0
      by_cases h : p.1 = q
      · rw [ite_eq_left h, ite_eq_left (by rw [← h])]
      · rw [ite_eq_right h, ite_eq_right (by intro h'; exact h (by rw [← h'])), map_zero]
    | zero =>
      convert V.zero_mem using 1
      funext p
      split_ifs <;> rfl
    | add g g' _ _ hg hg' =>
      convert V.add_mem hg hg' using 1
      funext p
      by_cases h : p.1 = q <;> simp [h]
    | smul c g _ hg =>
      convert V.smul_mem c hg using 1
      funext p
      by_cases h : p.1 = q <;> simp [h]
  rw [eq_top_iff]
  rintro v -
  have hv : v = ∑ q : Fin nT × Fin nS, (fun p : IxF F nS nT => if p.1 = q then v (q, p.2) else 0) := by
    funext p
    rw [Finset.sum_apply, Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  rw [hv]
  exact V.sum_mem fun q _ => key q (fun w => v (q, w))
end Span
end PositivityTheory.ThKW.TauSpanIdentities
end

noncomputable section
namespace PositivityTheory.ThKW
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF MeasureTheory
  GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT)
  E} {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E} {Λ : Submodule (𝓞
  E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ} {Om : GAF σ JS × GAF σ
  JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
variable {η : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}
theorem cut_char_k (hB : GoodK σ B) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {χ : (AEF F E)ˣ →* Circle} {m : ℕ} (hres : ResEtaF χ m) (hε : IsHalfF σ ε) {e : AEF F E} (he : IsSplitIdemF σ e)
    {g : GAF σ J} {x : (AEF F E)ˣ} (hg : SuppAtF σ e J g) (hx : IsDetAtF σ e J g x) :
    χ (GlobalTheory.SplitDetCharF.cutDet σ J ε hε.idem g) = χ x := by
  rcases hε.split e he with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · rw [GlobalTheory.SplitDetCharF.cutDet_same ε hε.idem a1 a2 hg hx]
  · exact GlobalTheory.SplitDetCharF.char_eq_of_mul_conj hB.cm hres _ x
      (GlobalTheory.SplitDetCharF.cutDet_conj hJ ε hε.idem he.1 a1 a2 hg hx)
theorem fin_inf_comm_A_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hO :
  IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) (p q : GAF σ JS × GAF σ JT) (f : WOF F E nS nT → ℂ)
    (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) : of p (oi q f) = oi q (of p f) := by
  obtain ⟨z, hz⟩ := hof p
  have hσ := LatA.sig_sig_k C.good
  obtain ⟨a, ha, k, hk, e1, -⟩ := _root_.GlobalTheory.WeilPartsF.exists_real_finite_mul F E σ nS JS q.1
  obtain ⟨b, hb, l, hl, e2, -⟩ := _root_.GlobalTheory.WeilPartsF.exists_real_finite_mul F E σ nT JT q.2
  have hoi : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → oi q f = oi (a, b) f := fun f h => by
    rw [show q = (a, b) * (k, l) from Prod.ext e1 e2, map_mul, mul_apply_eq_comp, hi.triv k hk l hl f h]
  let L : thetaSubF σ JS JT ξ₀ B.ψ →ₗ[ℂ] thetaSubF σ JS JT ξ₀ B.ψ := (oi q).restrict fun f hf => hi.pres q f hf
  have hL : ∀ m, (L m : WOF F E nS nT → ℂ) = oi q m := fun _ => rfl
  have := congrArg Subtype.val ((LatA.rep_k hO).comm
    (LatA.sys_k hσ C.hS C.hT C.hξ hO) L (fun x v => Subtype.ext (by
    have e3 : actOF σ JS JT a b x = x := by
      have := congrArg (fun y : XFF F E nS nT => (y : WOF F E nS nT)) (LatA.rhoFF_real ha hb x)
      rwa [coe_rhoFF] at this
    rw [hL, coe_opFF, coe_opFF, hL, map_smul, hoi _ (hc _ _ v.2), hi.Heisenberg₂ a ha b hb _ _ v.2, e3,
      ← hoi _ v.2])) p ⟨f, hf⟩)
  rw [hz ⟨f, hf⟩, map_smul, ← hL, ← this]
  exact hz (L ⟨f, hf⟩)
theorem eventually_smul_A_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hO :
  IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    {f : WOF F E nS nT → ℂ} (h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ f) :
    ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), ∃ c : ℂ, of p f = c • f := by
  filter_upwards [LatA.eventually_fix_k (LatA.sig_sig_k
    C.good) C.hS C.hT C.hξ hO ⟨f, h1⟩] with p hp
  obtain ⟨c, hc'⟩ := hof p
  exact ⟨c, by rw [hc' ⟨f, h1⟩, hp]⟩
theorem continuous_product_A_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hO :
  IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) {f : WOF F E nS nT → ℂ} (h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ f)
    (u : WOF F E nS nT) : Continuous fun p : GAF σ JS × GAF σ JT => of p (oi p f) u := by
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : IsTopologicalGroup (GAF σ JS) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JS))
  have : IsTopologicalGroup (GAF σ JT) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JT))
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h2 : Filter.Tendsto (fun p => p * q⁻¹) (𝓝 q) (𝓝 1) :=
    (continuous_id.mul continuous_const).tendsto' q 1 (mul_inv_cancel q)
  have h3 := hf.pres q f h1
  have h4 : ∀ᶠ p in 𝓝 q, ∃ c : ℂ, of p f = c • of q f := by
    filter_upwards [h2.eventually (eventually_smul_A_k C hO hof h3)] with p hp
    rwa [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel_right] at hp
  by_cases h0 : of q f = 0
  · refine continuousAt_const.congr (f := fun _ => (0 : ℂ)) ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc'⟩ := hp
    rw [fin_inf_comm_A_k C hO hof hi p p f h1, hc', h0, smul_zero, map_zero]
    rfl
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    have hx' : of q f x ≠ 0 := hx
    refine (((hf.cont f h1 x).div_const (of q f x)).mul (hi.cont _ h3 u)).continuousAt.congr ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc'⟩ := hp
    show of p f x / of q f x * oi p (of q f) u = _
    rw [fin_inf_comm_A_k C hO hof hi p p f h1, hc', map_smul, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul,
      mul_div_cancel_right₀ _ hx']
theorem datum_of_aut_A_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hO :
  IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hη : IsHeckeCharF η) (hres : ResEtaF η 1) (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (haut : ∀ γ ∈ GQF σ JS, ∀ γ' ∈ GQF σ JT, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of (γ, γ') (oi (γ, γ') f) 0 = f 0) :
    ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω := by
  have hB := C.good
  have hψ := GlobalTheory.T.standard_additive_character_sign F E σ B hB
  have hcomm : ∀ p q f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p (oi q f) = oi q (of p f) :=
    fun p q f h => fin_inf_comm_A_k C hO hof hi p q f h
  have hth : ∀ (w₀ : WOF F E nS nT) f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
      IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w₀ f) :=
    fun w₀ f h => _root_.GlobalTheory.HeisKeepF.isThetaFunOF_heisOF F E σ nS nT JS JT ξ₀ B.ψ hB.std.1 w₀ f h
  let Th := thetaSubF σ JS JT ξ₀ B.ψ
  let Om2 : GAF σ JS × GAF σ JT →* Module.End ℂ Th :=
    { toFun := fun p => (of p * oi p).restrict (p := Th) (q := Th) fun f h1 => hf.pres p _ (hi.pres p f h1)
      map_one' := LinearMap.ext fun f => Subtype.ext (by
        show of 1 (oi 1 f) = f
        simp only [map_one, one_apply_eq_self])
      map_mul' := fun p q => LinearMap.ext fun f => Subtype.ext (by
        show of (p * q) (oi (p * q) f) = of p (oi p (of q (oi q (f : WOF F E nS nT → ℂ))))
        simp only [map_mul, mul_apply_eq_comp]
        rw [hcomm q p _ (hi.pres q _ f.2)]) }
  obtain ⟨om, hom⟩ := exists_extend Th Om2
  have ho : ∀ p f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → om p f = of p (oi p f) := fun p f h1 => hom p ⟨f, h1⟩
  have hp : ∀ p f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (om p f) := fun p f h1 => by
    rw [ho p f h1]
    exact hf.pres p _ (hi.pres p f h1)
  refine ⟨om, hψ, isHeckeCharF_pow hη _, isHeckeCharF_pow hη _, resEtaF_pow hres _, resEtaF_pow hres _, hp,
    fun g h w₀ f h1 => ?_, fun γ hγ γ' hγ' f h1 => ?_, fun f h1 w => ?_, fun μ 𝓕 hμ h𝓕 p f h1 => ?_,
    fun e he g h hg hh x y hx hy => ?_⟩
  · obtain ⟨a, ha, k, hk, e1, e1'⟩ := _root_.GlobalTheory.WeilPartsF.exists_real_finite_mul F E σ nS JS g
    obtain ⟨b, hb, l, hl, e2, e2'⟩ := _root_.GlobalTheory.WeilPartsF.exists_real_finite_mul F E σ nT JT h
    have key : ∀ x, IsThetaFunOF σ JS JT ξ₀ B.ψ x → om (g, h) x = of (k, l) (oi (a, b) x) := fun x hx => by
      rw [ho _ x hx]
      have E1 : ((g, h) : GAF σ JS × GAF σ JT) = (a, b) * (k, l) := Prod.ext e1 e2
      have E2 : ((g, h) : GAF σ JS × GAF σ JT) = (k, l) * (a, b) := Prod.ext e1' e2'
      have E3 : oi (g, h) x = oi (a, b) x := by rw [E1, map_mul, mul_apply_eq_comp, hi.triv k hk l hl x hx]
      rw [E3, E2, map_mul, mul_apply_eq_comp, hf.triv a ha b hb _ (hi.pres _ x hx)]
    rw [key _ (hth w₀ f h1), key f h1, hi.Heisenberg₂ a ha b hb w₀ f h1, hf.Heisenberg₂ k hk l hl _ _ (hi.pres _ f h1),
      ← actOF_mul, ← e1', ← e2']
  · rw [ho _ f h1]
    exact haut γ hγ γ' hγ' f h1
  · have e : (fun p => om p f w) = fun p => of p (oi p f) w := funext fun p => by rw [ho p f h1]
    rw [e]
    exact continuous_product_A_k C hO hf hof hi h1 w
  · rw [ho p f h1, hf.unit μ 𝓕 hμ h𝓕 p _ (hi.pres p f h1), hi.unit μ 𝓕 hμ h𝓕 p f h1]
  · obtain ⟨r, hr, h2⟩ := hf.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f h1 => ?_⟩
    rw [ho _ f h1, hi.triv g (mem_GfCF_of_suppAt he hg) h (mem_GfCF_of_suppAt he hh) f h1]
    exact h2 ℓ hℓ f h1
end

section
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT)
  E} {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E} {Λ : Submodule (𝓞
  E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ} {Om : GAF σ JS × GAF σ
  JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)} {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
variable {η : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}
theorem fin_inf_comm_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hO : IsLatRepL
  σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) (p q : GAF σ JS × GAF σ JT) (f : WOF F E nS nT → ℂ)
    (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) : of p (oi q f) = oi q (of p f) :=
  fin_inf_comm_A_k C hO hof hi p q f hf
theorem datum_of_aut_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hO :
  IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (h1 : IsHeckeCharF η) (h2 : ResEtaF η 1) (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (haut : ∀ γ ∈ GQF σ JS, ∀ γ' ∈ GQF σ JT, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of (γ, γ') (oi (γ, γ') f) 0 = f 0) :
    ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω :=
  datum_of_aut_A_k C hO h1 h2 hf hof hi haut
end
end PositivityTheory.ThKW
end
