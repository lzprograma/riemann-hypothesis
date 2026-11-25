module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticTraceFormAlternatingSwap
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicActionRealCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHeisenbergOperatorBoundedThetaFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFdPosFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicAddRealChartPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergSmoothOfWeakDerivativeClosedSet
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormRealCoordinateMatrixHermitianDetNeZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralGaussianRealIsometryNoFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralEqOfHeisenbergInvariantNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedModelThetaFunctionBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealCoordinateActionUnitaryPreservesHermitianFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionSmoothVectorRealHeisenberg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRealPointsFixFiniteAdelicHoms
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ArchimedeanChartGaussianInvariant
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFinsetAnnLeK
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutRealA
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutSubstA
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IsScalarOneOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCMRealLineAddNoPhase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDistributionInvariantRationalTarget
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalvedSymplecticFormFiniteRealOrthogonal
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SpanInfRatF

/-! # RedWpDatum: Consolidated global theta-kernel definitions and proofs (RedWpDatum). -/
@[expose] public section

open UpperTheory.TP.W (GoodK)
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open PositivityTheory.ThKW (Ctx_k)
open Units (map)

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
  MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealWeil
  GlobalTheory.RealWeilF Classical
noncomputable section
namespace GlobalTheory.ThetaSmoothF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem contDiff_heis_iota_k (σ : E →ₐ[F] E) (B : Base F E) (hB : GoodK σ B) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E} (hι : IsChartF θ ι)
    {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) (x : WOF F E nS nT) :
    ContDiff ℝ ∞ fun v : IxF F nS nT → ℂ => heisOF σ JS JT ξ₀ B.ψ (iotaVF ι v) f x := by
  obtain ⟨lam, hl,
    hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log (GlobalTheory.T.standard_additive_character_sign F E σ B hB)
  let φ : (IxF F nS nT → ℂ) →+ ℂ :=
    { toFun := fun v => lam (symplOHF σ JS JT ξ₀ x (iotaVF ι v))
      map_zero' := by rw [iotaVF_zero, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero]
      map_add' := fun u v => by rw [iotaVF_add, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add (f := _)] }
  have hφ : Continuous φ := hl.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ x (continuous_iotaVF hι))
  let eqv := (Module.finBasis ℝ (IxF F nS nT → ℂ)).equivFunL
  let L' : (Fin (Module.finrank ℝ (IxF F nS nT → ℂ)) → ℝ) →+ WOF F E nS nT :=
    (iotaHom ι).comp eqv.symm.toLinearEquiv.toAddMonoidHom
  have hL' : Continuous L' := (continuous_iotaVF hι).comp eqv.symm.continuous
  have hsm := hf.smooth _ L' hL' (fun t => real_iotaVF hι _) x
  have hg : ContDiff ℝ ∞ fun v : IxF F nS nT → ℂ => f (x + iotaVF ι v) := by
    have h1 := hsm.comp eqv.contDiff
    convert h1 using 1
    funext v
    simp [L', iotaHom]
  have e : (fun v : IxF F nS nT → ℂ => heisOF σ JS JT ξ₀ B.ψ (iotaVF ι v) f x) =
      fun v => Complex.exp (φ.toRealLinearMap hφ v) * f (x + iotaVF ι v) := by
    funext v
    rw [heisOF, hlam _ (GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ x _ (real_iotaVF hι v))]
    rfl
  rw [e]
  exact ((φ.toRealLinearMap hφ).contDiff.cexp).mul hg
end GlobalTheory.ThetaSmoothF
open GlobalTheory.ThetaSmoothF in
theorem GlobalTheory.ThetaSmoothF.sm_of_thetaF_k : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E),
      GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 →
        Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' θ hθ ι hι hψ f hf
  have hstd := GlobalTheory.T.standard_additive_character_sign F E σ B hB
  let H := HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)
  let B₀ : (IxF F nS nT → ℂ) →ₗ[ℝ] (IxF F nS nT → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => (star y ⬝ᵥ H *ᵥ x).im)
      (fun x x' y => by simp [Matrix.mulVec_add, dotProduct_add])
      (fun c x y => by simp [Matrix.mulVec_smul, dotProduct_smul])
      (fun x y y' => by simp [add_dotProduct])
      (fun c x y => by simp [star_smul, smul_dotProduct])
  let om :=
    LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap (𝕜 := ℝ)).toLinearMap ∘ₗ B₀)
  have e : (fun x y => om x y) = fun x y => (star y ⬝ᵥ H *ᵥ x).im := rfl
  have hH : IsHeis (fun x y : IxF F nS nT → ℂ => (star y ⬝ᵥ H *ᵥ x).im) (rhoVF σ JS JT ξ₀ B.ψ hψ ι) := by
    refine ⟨fun g => ?_, fun u v g => ?_, fun u g => norm_rhoBF hψ _ g, fun g => ?_⟩
    · show rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι 0) g = g
      rw [iotaVF_zero]
      exact rhoBF_zero hψ g
    · show rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι u) (rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι v) g) =
        _ • rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι (u + v)) g
      rw [rhoBF_rhoBF, iotaVF_add,
        GlobalTheory.T.archimedean_chart_theta_equivariant F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' θ hθ ι hι u v]
    · exact (_root_.GlobalTheory.RealWeilF.continuous_rhoBF F E σ nS nT JS JT ξ₀ B.ψ hψ g).comp
        (continuous_iotaVF hι)
  refine _root_.GlobalTheory.RealWeil.sm_of_weak_deriv_closed (IxF F nS nT → ℂ) (BBF σ JS JT ξ₀ B.ψ) om (rhoVF
    σ JS JT ξ₀ B.ψ hψ ι) (e ▸ hH)
    (WOF F E nS nT) (ev _ _) norm_ev_le (fun b C => norm_QB_le b)
    (fun x v => ⟨B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)), x + iotaVF ι v, fun b => rfl⟩)
    {g | IsThetaFunOF σ JS JT ξ₀ B.ψ g.1} ?_ ?_ f hf
  · intro g hg x
    exact (GlobalTheory.ThetaSmoothF.contDiff_heis_iota_k σ B hB JS JT ξ₀ hι hg x).differentiable (by simp)
  · intro g hg z
    let L : ℝ →+ WOF F E nS nT :=
      { toFun := fun t => iotaVF ι (t • z)
        map_zero' := by rw [zero_smul, iotaVF_zero]
        map_add' := fun s t => by rw [add_smul, iotaVF_add] }
    have hL : Continuous L := (continuous_iotaVF hι).comp (continuous_id.smul continuous_const)
    have hL0 : ∀ t, (L t).map (finPartF F E) = 0 := fun t => real_iotaVF hι _
    let d : WOF F E nS nT → ℂ := fun w => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g.1 w) 0
    have hlev : ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u d = d := by
      obtain ⟨U, hU, hUf⟩ := hg.level
      exact ⟨U, hU, fun u hu hu0 =>
        GlobalTheory.T.theta_function_rapid_decay F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 L hL hL0 u hu0
          (hUf u hu hu0)⟩
    have hsm : ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L' →
        (∀ t, (L' t).map (finPartF F E) = 0) → ∀ w, ContDiff ℝ ∞ fun t => d (w + L' t) :=
      fun k L' hL' hL'0 w => GlobalTheory.T.theta_function_integrable F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd
        g.1 hg L hL hL0 k L' hL' hL'0 w
    have hd : IsThetaFunOF σ JS JT ξ₀ B.ψ d :=
      ⟨fun γ w => GlobalTheory.T.theta_function_moderate_growth F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1
        hg L hL hL0 γ w, hlev,
        GlobalTheory.T.theta_integral_unfolding F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd d hlev hsm, hsm⟩
    have hb := _root_.GlobalTheory.TowerFD.thetaFunOF_bounded F E σ nS nT JS JT ξ₀ B.ψ hψ d hd
    refine ⟨toBF d hd.cont hb hd.quasi, hd, fun x => ?_⟩
    exact (GlobalTheory.T.theta_function_smooth_vectors F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 hg L hL
      hL0 x).hasDerivAt
end
end

abbrev _root_.GlobalTheory.T.archimedean_chart_gaussian_norm :=
  GlobalTheory.ThetaSmoothF.sm_of_thetaF_k

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
  MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealWeil
  GlobalTheory.RealWeilF Classical
noncomputable section
namespace GlobalTheory.RealWeilF
theorem mMF_unitary_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E),
      GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ p : GAF σ JS × GAF σ JT,
        (mMF σ JS JT θ p)ᴴ * HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) * mMF σ JS JT θ p = HMF JS JT ξ₀ (fun
        w : InfinitePlace F => (B.emb w).1) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ θ hθ ι _ p
  obtain ⟨g, h⟩ := p
  have hσ : ∀ w x, (B.emb w).1 (σ x) = star ((B.emb w).1 x) := fun w x => hB.cm.2.2.2 _ x
  unfold HMF
  rw [mMF_apply, blk_conjTranspose, blk_mul, blk_mul]
  congr 1 <;> funext w
  · rw [Matrix.mul_smul, Matrix.smul_mul, compAtF_unitary hσ hθ]
  · have h1 := compAtF_unitary hσ hθ JS g w
    have h2 := compAtF_mul_inv θ JS g w
    conv_rhs => rw [← h1, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv, inv_eq_right_inv h2]
end GlobalTheory.RealWeilF
end
end

abbrev _root_.GlobalTheory.T.archimedean_chart_gaussian_vector :=
  GlobalTheory.RealWeilF.mMF_unitary_k

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
  MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealWeil
  GlobalTheory.RealWeilF Classical
noncomputable section
namespace GlobalTheory.RealWeilF.MCont
theorem continuous_mMF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F]
  E)
    (B : Base F E),
      GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E)
      (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → Continuous (mMF σ JS JT θ) := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT θ hθ
  have hc : ∀ (w : InfinitePlace F) (m n : ℕ), Continuous fun x : Matrix (Fin m) (Fin n) (AEF F E) => compAtF θ w x :=
    fun w m n => continuous_id.matrix_map (continuous_comp_infPartF (hθ w))
  have h1 : Continuous fun p : GAF σ JS × GAF σ JT => mtF σ JT p.2 :=
    (Units.continuous_val.comp continuous_subtypeVal).comp continuous_snd
  have h2 : Continuous fun p : GAF σ JS × GAF σ JT => mtF σ JS p.1⁻¹ := by
    have : (fun g : GAF σ JS => mtF σ JS g⁻¹) =
        fun g => (((Subtype.val (show HR (AF F) σ JS from g))⁻¹ : GL (Fin nS) (AF F ⊗[F] E)) : Matrix _ _ _) := rfl
    have hi : Continuous fun g : GAF σ JS => mtF σ JS g⁻¹ := by
      rw [this]; exact Units.continuous_coe_inv.comp continuous_subtypeVal
    exact hi.comp continuous_fst
  have e : (mMF σ JS JT θ : GAF σ JS × GAF σ JT → _) = fun p =>
      GlobalTheory.RealWeil.blk (fun w => compAtF θ w (mtF σ JT p.2)) fun w => compAtF θ w (mtF σ JS p.1⁻¹) := funext
        fun p => rfl
  rw [e]
  exact GlobalTheory.RealWeil.continuous_blk (fun w => (hc w _ _).comp h1) fun w => (hc w _ _).comp h2
end GlobalTheory.RealWeilF.MCont
end
end

abbrev _root_.GlobalTheory.T.continuous_moment_map :=
  GlobalTheory.RealWeilF.MCont.continuous_mMF_k

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
  MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealWeil
  GlobalTheory.RealWeilF Classical
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem GlobalTheory.RealWeilF.HMF_herm_det_k : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E),
      GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1))ᴴ = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) ∧
        (HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)).det ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ h0 hσ
  exact GlobalTheory.RealWeilF.hermitianFormRealCoordinateBlock_hermitian_det σ hB.cm.2.2.2 JS JT hS hT ξ₀ h0 hσ _
end

abbrev _root_.GlobalTheory.T.hermitian_form_matrix_selfadjoint :=
  GlobalTheory.RealWeilF.HMF_herm_det_k
end

noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
  GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DatumF MeasureTheory
namespace GlobalTheory.ThetaSchurF
theorem schur_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B :
  Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ M : Module.End ℂ (WOF F E nS nT → ℂ),
      (∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f)) →
      (∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ w f) = heisOF σ JS JT ξ₀ B.ψ w (M f)) →
      (∀ (μ : MeasureTheory.Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
        MeasureTheory.IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) →
      ∃ c : ℂ, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ M hM hc hn
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).1
  have hinv : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  have hskew := _root_.GlobalTheory.SymplSkew.symplOF_swap F E σ hinv nS nT JS JT hJS hJT ξ₀ hσξ
  have hann := GlobalTheory.T.rational_lattice_self_dual F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ
  have hth : ∀ w f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w f) :=
    fun w f hf => GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ w f hf
  have h2 : ∀ f f', IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ f' → ∀ x y,
      M f x * star (M f' y) = f x * star (f' y) := fun f f' hf hf' x y => by
    have h := prod_eq hψ hskew hann hth M hM hc hn hf (hth (y - x) f' hf') x
    rw [hc _ _ hf'] at h
    simp only [heisOF, add_sub_cancel, star_mul'] at h
    linear_combination B.ψ (symplOHF σ JS JT ξ₀ x (y - x)) * h -
      (M f x * star (M f' y) - f x * star (f' y)) * mul_star_psi hψ.2.1 (symplOHF σ JS JT ξ₀ x (y - x))
  by_cases h0 : ∃ f₀ y, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ y ≠ 0
  · obtain ⟨f₀, y, hf₀, hy⟩ := h0
    have h1 := h2 f₀ f₀ hf₀ hf₀ y y
    have hn1 : ‖M f₀ y‖ = ‖f₀ y‖ := by
      have := congrArg norm h1
      rw [norm_mul, norm_mul, norm_star, norm_star] at this
      exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).1 this
    have hy' : M f₀ y ≠ 0 := by
      rw [← norm_ne_zero_iff, hn1]
      exact norm_ne_zero_iff.2 hy
    have hs := star_ne_zero.2 hy'
    refine ⟨star (f₀ y) / star (M f₀ y), fun f hf => ?_⟩
    funext x
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h2 f f₀ hf hf₀, mul_comm]
  · refine ⟨1, fun f hf => ?_⟩
    have : f = 0 := funext fun y => by
      by_contra hy
      exact h0 ⟨f, y, hf, hy⟩
    rw [this, map_zero, smul_zero]
end GlobalTheory.ThetaSchurF
end

noncomputable section
open scoped Classical ComplexOrder Kronecker Matrix TensorProduct Topology ContDiff
open Formalism.IndefR.DatumF Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinLatF
  GlobalTheory.FinWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.LFun
  GlobalTheory.RealWeilF GlobalTheory.WeilM GlobalTheory.WeilPartsF IsDedekindDomain Matrix MeasureTheory NumberField
  GlobalTheory.RealWeil
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E} {ψ :
  AddChar (AF F) ℂ}
variable {B : Base F E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
theorem exists_inf_A_k (C : Ctx_k σ B JS JT ξ₀ θ ι) : ∃ oi, IsInfWeilF σ JS JT ξ₀ B.ψ oi ∧
    ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → ((HMF JS JT ξ₀ (tauB B)) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f := by
  have hB := C.good
  have hc : IsCharAF F B.ψ := (GlobalTheory.T.standard_additive_character_sign F E σ B hB).1
  have hθ := C.inf
  have hι := C.chart
  have hS := C.hS
  have hT := C.hT
  have hξ := C.h0
  have hξσ := C.hξ
  have hH := GlobalTheory.T.hermitian_form_matrix_selfadjoint F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ
  have hHeis : IsHeis (fun x y => (star y ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ x).im)
      (rhoVF σ JS JT ξ₀ B.ψ hc ι) := by
    refine ⟨fun f => ?_, fun u v f => ?_, fun u f => norm_rhoBF hc _ f, fun f => ?_⟩
    · show rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι 0) f = f
      rw [iotaVF_zero, rhoBF_zero]
    · show rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι u) (rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι v) f) =
        _ • rhoBF σ JS JT ξ₀ B.ψ hc (iotaVF ι (u + v)) f
      rw [rhoBF_rhoBF, iotaVF_add, GlobalTheory.T.archimedean_chart_theta_equivariant F E σ B hB nS nT JS JT hS
        hT ξ₀ hξ hξσ θ hθ ι hι]
    · exact (_root_.GlobalTheory.RealWeilF.continuous_rhoBF F E σ nS nT JS JT ξ₀ B.ψ hc f).comp
        (continuous_iotaVF hι)
  obtain ⟨Ω, ⟨hadd, hsmul, hsm, hone, hmul, hheis, hcomm, hunit⟩, htriv, hcont, hvac⟩ :=
    _root_.GlobalTheory.RealWeil.UnitaryOsc.exists_osc (IxF F nS nT) (HMF JS JT ξ₀ (fun w : InfinitePlace F
      => (B.emb w).1)) hH.1 hH.2
      (BBF σ JS JT ξ₀ B.ψ) (rhoVF σ JS JT ξ₀ B.ψ hc ι) hHeis (GAF σ JS × GAF σ JT) (mMF σ JS JT θ)
      (GlobalTheory.T.archimedean_chart_gaussian_vector F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι)
  have sm := GlobalTheory.T.archimedean_chart_gaussian_norm F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι hc
  have hfr := _root_.GlobalTheory.WeilDatumF.symplOHF_fin_real_orth F E σ nS nT JS JT ξ₀
  have rcomm : ∀ {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ (v : IxF F nS nT → ℂ) (f : BBF σ JS JT ξ₀ B.ψ),
      rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v f) =
        rhoVF σ JS JT ξ₀ B.ψ hc ι v (rhoBF σ JS JT ξ₀ B.ψ hc u f) := by
    intro u hu v f
    unfold rhoVF
    rw [rhoBF_rhoBF, rhoBF_rhoBF, (hfr u _ hu (real_iotaVF hι v)).1, (hfr u _ hu (real_iotaVF hι v)).2, add_comm]
  have radd : ∀ {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ (v : IxF F nS nT → ℂ) (f : BBF σ JS JT ξ₀ B.ψ),
      rhoBF σ JS JT ξ₀ B.ψ hc (u + iotaVF ι v) f = rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v f) := by
    intro u hu v f
    unfold rhoVF
    rw [rhoBF_rhoBF, (hfr u _ hu (real_iotaVF hι v)).1, AddChar.map_zero_eq_one, one_smul]
  have hfin : ∀ p {u : WOF F E nS nT}, u.map (infPartF F E) = 0 → ∀ f : BBF σ JS JT ξ₀ B.ψ,
      Sm (rhoVF σ JS JT ξ₀ B.ψ hc ι) f → Ω p (rhoBF σ JS JT ξ₀ B.ψ hc u f) = rhoBF σ JS JT ξ₀ B.ψ hc u (Ω p f) :=
    fun p u hu f hf => hcomm p _ (fun v g => rcomm hu v g) f hf
  have hth : ∀ p (f : BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 → IsThetaFunOF σ JS JT ξ₀ B.ψ (Ω p f).1 := by
    intro p f hf
    obtain ⟨U, hU, hl⟩ := hf.level
    refine GlobalTheory.T.archimedean_chart_gaussian_invariant F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι hι
      hc _ (hsm p f (sm f hf)) ⟨U, hU, fun u hu h0 => ?_⟩
    have e : rhoBF σ JS JT ξ₀ B.ψ hc u f = f := QB_ext fun x => congrFun ((coe_rhoBF hc u f).trans (hl u hu h0)) x
    rw [← coe_rhoBF hc, ← hfin p h0 f (sm f hf), e]
  have hbd := _root_.GlobalTheory.TowerFD.thetaFunOF_bounded F E σ nS nT JS JT ξ₀ B.ψ hc
  obtain ⟨om, hom⟩ := exists_homF hbd Ω hth (fun p f f' h1 h2 => hadd p f f' (sm f h1) (sm f' h2))
    (fun p a f h1 => hsmul p a f (sm f h1)) (fun f h1 => hone f (sm f h1)) fun p p' f h1 => hmul p p' f (sm f h1)
  have lift : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∃ G : BBF σ JS JT ξ₀ B.ψ, (G.1 : WOF F E nS nT → ℂ) = f :=
    fun f hf => ⟨toBF f hf.cont (hbd f hf) hf.quasi, rfl⟩
  refine ⟨om, ⟨⟨fun p f hf => ?_, fun f hf w => ?_, fun μ 𝓕 hμ h𝓕 p f hf => ?_⟩, fun g hg k hk f hf => ?_,
    fun g hg k hk w f hf => ?_⟩, fun s hs hpos p hsc f hf hv => ?_⟩ <;> obtain ⟨G, rfl⟩ := lift f hf
  · rw [hom p G hf]
    exact hth p G hf
  · simp only [hom _ G hf]
    exact (ev _ _ w).continuous.comp
      (hcont (GlobalTheory.T.continuous_moment_map F E σ B hB nS nT JS JT θ hθ) G (sm G hf))
  · rw [hom p G hf]
    exact _root_.GlobalTheory.RealWeilF.lintegral_eq_of_normsF F E σ nS nT JS JT ξ₀ B.ψ hc μ 𝓕 hμ h𝓕 _ _
      fun H _ _ _ Φ hΦ => hunit H Φ (fun v g => hΦ _ g) p G (sm G hf)
  · rw [hom _ G hf, htriv _ (mMF_fin θ hg hk) G (sm G hf)]
  · obtain ⟨u, v, hu, rfl⟩ := _root_.GlobalTheory.RealWeilF.exists_realZero_add_iotaVF F E nS nT θ ι hι w
    have h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ (rhoVF σ JS JT ξ₀ B.ψ hc ι v G).1 :=
      GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ _ _ hf
    have h2 : IsThetaFunOF σ JS JT ξ₀ B.ψ (rhoBF σ JS JT ξ₀ B.ψ hc u (rhoVF σ JS JT ξ₀ B.ψ hc ι v G)).1 :=
      GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ _ _ h1
    have e1 : actOF σ JS JT g k (u + iotaVF ι v) = u + iotaVF ι (mMF σ JS JT θ (g, k) *ᵥ v) := by
      rw [GlobalTheory.RealWeilF.actOF_add, _root_.GlobalTheory.RealWeilFinFix.actOF_fin F E σ nS nT JS JT g k
        hg hk u hu, GlobalTheory.T.actOF_iotaVF_eq_iotaVF_mulVec F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξσ θ hθ ι
        hι]
    rw [hom _ G hf, e1, ← coe_rhoBF hc _ G, ← coe_rhoBF hc _ (Ω (g, k) G), radd hu v G,
      radd hu _ (Ω (g, k) G), hom _ _ h2, hfin _ hu _ (sm _ h1), hheis _ _ _ (sm G hf)]
  · rw [hom _ G hf, hvac s p hs hpos hsc G (sm G hf) (fderiv_vacF hc ι s G (sm G hf) hv)]
    rfl
end PositivityTheory.ThKW
end

noncomputable section
namespace PositivityTheory.ThKW
open scoped Classical ComplexOrder Kronecker Matrix TensorProduct Topology
open Formalism.IndefR.DatumF Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinLatF
  GlobalTheory.FinWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.LFun
  GlobalTheory.RealWeilF GlobalTheory.WeilM GlobalTheory.WeilPartsF IsDedekindDomain Matrix MeasureTheory NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section
section
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT)
  E} {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
theorem det_mMF_B_k (C : Ctx_k σ B JS JT ξ₀ θ ι) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    (mMF σ JS JT θ (g⁻¹, h⁻¹)).det = ∏ v, tauB B v (b ⊗ₖ aᵀ).det ∧
      (mMF σ JS JT θ (g⁻¹, h⁻¹) - 1).det = ∏ v, tauB B v (b ⊗ₖ aᵀ - 1).det := by
  have e1 : ∀ w, compAtF θ w (mtF σ JT h⁻¹) = b.map (tauB B w) := fun w => by
    rw [hb]
    ext i j
    exact RealC.theta_inc (C.inf w) _
  have e2 : ∀ w, compAtF θ w (mtF σ JS g⁻¹⁻¹) = a.map (tauB B w) := fun w => by
    rw [inv_inv, ha]
    ext i j
    exact RealC.theta_inc (C.inf w) _
  have e3 : ∀ w, (b.map (tauB B w) ⊗ₖ (a.map (tauB B w))ᵀ) = (b ⊗ₖ aᵀ).map (tauB B w) := fun w => by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.map_apply, Matrix.transpose_apply, map_mul]
  rw [mMF_apply]
  simp only [e1, e2]
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.RatAut.RealInt.det_blk]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [e3]
    exact (RingHom.map_det _ _).symm
  · rw [GlobalTheory.RatAut.RealInt.det_blk_sub_one]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [e3, RingHom.map_det, map_sub, map_one]
    rfl
end

section
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT)
  E} {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E} {Λ : Submodule (𝓞
  E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ} {Om : GAF σ JS × GAF σ
  JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)} {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
theorem exists_inf_k (C : Ctx_k σ B JS JT ξ₀ θ ι) : ∃ oi, IsInfWeilF σ JS JT ξ₀ B.ψ oi ∧
    ∀ s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ, s * s = 1 → ((HMF JS JT ξ₀ (tauB B)) * s).PosDef → ∀ p,
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsVacF σ JS JT ξ₀ B.ψ ι s f →
        oi p f = GlobalTheory.RealWeil.dP s (mMF σ JS JT θ p) • f :=
  exists_inf_A_k C
theorem det_mMF_k (C : Ctx_k σ B JS JT ξ₀ θ ι) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    (mMF σ JS JT θ (g⁻¹, h⁻¹)).det = ∏ v, tauB B v (b ⊗ₖ aᵀ).det ∧
      (mMF σ JS JT θ (g⁻¹, h⁻¹) - 1).det = ∏ v, tauB B v (b ⊗ₖ aᵀ - 1).det :=
  det_mMF_B_k C ha hb

theorem rat_subst_k (C : Ctx_k σ B JS JT ξ₀ θ ι) {γ : GAF σ JS} (hγ : γ ∈ GQF σ JS) {γ' :
  GAF σ JT} (hγ' : γ' ∈ GQF σ JT)
    {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) :
    IsThetaFunOF σ JS JT ξ₀ B.ψ (fun x => f (actOF σ JS JT γ⁻¹ γ'⁻¹ x)) ∧
    (∀ w₀, (fun x => heisOF σ JS JT ξ₀ B.ψ w₀ f (actOF σ JS JT γ⁻¹ γ'⁻¹ x)) =
      heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT γ γ' w₀) (fun x => f (actOF σ JS JT γ⁻¹ γ'⁻¹ x))) ∧
    ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ →
        ∫⁻ x in 𝓕, ‖f (actOF σ JS JT γ⁻¹ γ'⁻¹ x)‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ := by
  have hψ : ∀ a, ‖B.ψ a‖ = 1 := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B C.good).1.2.1
  have hi := (GQF σ JS).inv_mem hγ
  have hi' := (GQF σ JT).inv_mem hγ'
  have hinv : ∀ x, actOF σ JS JT γ γ' (actOF σ JS JT γ⁻¹ γ'⁻¹ x) = x := fun x => by
    have := SubstA.actOF_inv_actOF (σ := σ) (JS := JS) (JT := JT) γ⁻¹ γ'⁻¹ x
    rwa [inv_inv, inv_inv] at this
  refine ⟨SubstA.isThetaFunOF_comp C.hS hf hi hi', fun w₀ => ?_, fun μ 𝓕 hμ h𝓕 => ?_⟩
  · funext x
    unfold heisOF
    beta_reduce
    rw [GlobalTheory.FinLatF.actOF_add, SubstA.actOF_inv_actOF, ← SubstA.symplOHF_actOF C.hS γ⁻¹ γ'⁻¹ x,
      SubstA.actOF_inv_actOF]
  · let e : WOF F E nS nT ≃+ WOF F E nS nT :=
      { toFun := actOF σ JS JT γ⁻¹ γ'⁻¹
        invFun := actOF σ JS JT γ γ'
        left_inv := hinv
        right_inv := SubstA.actOF_inv_actOF γ γ'
        map_add' := GlobalTheory.FinLatF.actOF_add _ _ }
    refine SubstA.setLIntegral_comp e (SubstA.continuous_actOF _ _) (SubstA.continuous_actOF _ _)
      (fun x => ⟨fun hx => ?_, SubstA.actOF_mem_ratLF hi hi'⟩) μ hμ h𝓕 (fun w => ‖f w‖ₑ ^ 2) ?_
    · rw [← hinv x]
      exact SubstA.actOF_mem_ratLF hγ hγ' hx
    · rintro _ ⟨y, rfl⟩ x
      have h7 : ‖f (ratWF y + x)‖ = ‖f x‖ := by
        rw [hf.quasi y x, norm_mul, hψ, one_mul]
      show ‖f (ratWF y + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2
      rw [← ofReal_norm, ← ofReal_norm, h7]
theorem schur_norm_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (M : Module.End ℂ (WOF F E nS nT → ℂ))
    (h1 : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (M f))
    (h2 : ∀ u f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M (heisOF σ JS JT ξ₀ B.ψ u f) = heisOF σ JS JT ξ₀ B.ψ u (M f))
    (h3 : ∀ (μ : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 μ → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        ∫⁻ x in 𝓕, ‖M f x‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → M f = c • f := by
  obtain ⟨c, hc⟩ := GlobalTheory.ThetaSchurF.schur_k F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ M h1 h2 h3
  have hψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B C.good).1.2.1
  by_cases h0 : ∃ f y, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ f y ≠ 0
  · obtain ⟨f, y, hf, hy⟩ := h0
    obtain ⟨μ, 𝓕, hμ, h𝓕, hI0, hIt⟩ := GlobalTheory.ThetaSchurUnitF.exists_fd_pos_fin hψ hf hy
    have h := h3 μ 𝓕 hμ h𝓕 f hf
    rw [hc f hf] at h
    simp only [Pi.smul_apply, smul_eq_mul, eNorm_mul, mul_pow] at h
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top eNorm_ne_top)] at h
    have e1 : ‖c‖ₑ ^ 2 = 1 := by
      have := congrArg (· / ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) h
      rwa [ENNReal.mul_div_cancel_right hI0 hIt, ENNReal.div_self hI0 hIt] at this
    have e2 : (‖c‖₊ : ENNReal) ^ 2 = 1 := by rwa [eNorm_eq_nnNorm] at e1
    have e3 : ‖c‖₊ ^ 2 = 1 := by exact_mod_cast e2
    have e4 : ‖c‖ ^ 2 = 1 := by
      have := congrArg (fun t : NNReal => (t : ℝ)) e3
      simpa using this
    exact ⟨c, (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 e4, hc⟩
  · push Not at h0
    refine ⟨1, norm_one, fun f hf => ?_⟩
    have : f = 0 := funext fun y => h0 f y hf
    subst this
    simp
end

section
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT)
  E} {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E} {Λ : Submodule (𝓞
  E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ} {Om : GAF σ JS × GAF σ
  JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)} {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
variable {η : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}
theorem exists_isScalarF_k (C : Ctx_k σ B JS JT ξ₀ θ ι) {χS χT : (AEF F E)ˣ →* Circle}
    (hf : IsFinWeilF σ JS JT ξ₀ B.ψ χS χT of) (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    {p : GAF σ JS × GAF σ JT} (h1 : p.1 ∈ GQF σ JS) (h2 : p.2 ∈ GQF σ JT) : ∃ c : ℂ, ‖c‖ = 1 ∧
      IsScalarF B ξ₀ of oi p c := by
  have R := fun f h => rat_subst_k C (inv_mem h1) (inv_mem h2) (f := f) h
  have R' := fun f h => rat_subst_k C h1 h2 (f := f) h
  obtain ⟨a, k, a1, a2, k1, k2, e1, e2⟩ := exists_partsF p
  have hoi : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → oi p f = oi a f := fun f h => by
    rw [e1, map_mul, mul_apply_eq_comp, hi.triv k.1 k1 k.2 k2 f h]
  have hof : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p f = of k f := fun f h => by
    rw [e2, map_mul, mul_apply_eq_comp, hf.triv a.1 a1 a.2 a2 f h]
  have hth := GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B C.good nS nT JS JT ξ₀
  obtain ⟨c, hc, h⟩ := schur_norm_k C (of p * oi p * substF σ JS JT p⁻¹)
    (fun f h => hf.pres _ _ (hi.pres _ _ (R f h).1))
    (fun u f h => by
      have t1 : IsThetaFunOF σ JS JT ξ₀ B.ψ (substF σ JS JT p⁻¹ f) := (R f h).1
      have t2 : substF σ JS JT p⁻¹ (heisOF σ JS JT ξ₀ B.ψ u f) =
        heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT p.1⁻¹ p.2⁻¹ u) (substF σ JS JT p⁻¹ f) := (R f h).2.1 u
      simp only [mul_apply_eq_comp]
      rw [t2, hoi _ (hth _ _ t1), hi.Heisenberg₂ a.1 a1 a.2 a2 _ _ t1, hof _ (hth _ _ (hi.pres _ _ t1)),
        hf.Heisenberg₂ k.1 k1 k.2 k2 _ _ (hi.pres _ _ t1), ← actOF_mul, ← actOF_mul, ← hof _ (hi.pres _ _ t1),
          ← hoi _ t1,
        show k.1 * a.1 = p.1 from congrArg Prod.fst e2.symm, show k.2 * a.2 = p.2 from congrArg Prod.snd e2.symm,
        mul_inv_cancel, mul_inv_cancel, GlobalTheory.FinLatF.actOF_one])
    (fun μ 𝓕 hμ h𝓕 f h => by
      have t1 : IsThetaFunOF σ JS JT ξ₀ B.ψ (substF σ JS JT p⁻¹ f) := (R f h).1
      simp only [mul_apply_eq_comp]
      rw [hf.unit μ 𝓕 hμ h𝓕 _ _ (hi.pres _ _ t1), hi.unit μ 𝓕 hμ h𝓕 _ _ t1]
      exact (R f h).2.2 μ 𝓕 hμ h𝓕)
  refine ⟨c, hc, fun f hf' => ?_⟩
  have := h (substF σ JS JT p f) (R' f hf').1
  simp only [mul_apply_eq_comp] at this
  rwa [← substF_mul, inv_mul_cancel, substF_one] at this
theorem IsScalarF.mul_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (hcomm : ∀ p q f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p (oi q f) = oi q (of p f)) {p q : GAF σ JS × GAF σ JT} {c c' :
      ℂ}
    (h : IsScalarF B ξ₀ of oi p c) (h' : IsScalarF B ξ₀ of oi q c') (h1 : q.1 ∈ GQF σ JS) (h2 : q.2 ∈ GQF σ JT) :
    IsScalarF B ξ₀ of oi (p * q) (c * c') := fun f hf => by
  have t : IsThetaFunOF σ JS JT ξ₀ B.ψ (substF σ JS JT q f) := (rat_subst_k C h1 h2 hf).1
  rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, hcomm q p _ (hi.pres _ _ hf), h' f hf, map_smul,
    map_smul, h _ t, smul_smul, mul_comm c', substF_mul]
theorem half_add_k (hB : GoodK σ B) (hε : IsHalfF σ ε) : (ε + cAF σ ε) * (ε + cAF σ ε) = ε + cAF
  σ ε := by
  have h3 : cAF σ ε * cAF σ ε = cAF σ ε := by rw [← map_mul, hε.idem]
  linear_combination hε.idem + h3 + 2 * hε.orth
theorem eta_cut_k (hB : GoodK σ B) (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) (u : Eˣ) :
    η (cutRat _ (half_add_k hB hε) u) * η (cutRat ε hε.idem (map (σ : E →* E) u)) = η
      (cutRat ε hε.idem u) := by
  have h3 : cAF σ ε * cAF σ ε = cAF σ ε := by rw [← map_mul, hε.idem]
  have e1 : cutRat _ (half_add_k hB hε) u = cutRat ε hε.idem u * cutRat _ h3 u :=
    Units.ext (by
    rw [Units.val_mul, cutRat_val, cutRat_val, cutRat_val]
    linear_combination (-(incAF F E u - 1) ^ 2) * hε.orth)
  have e2 := GlobalTheory.SplitDetCharF.char_norm hB.cm h2 (cutRat _ h3 u) (cutRat ε hε.idem (map (σ : E →* E) u))
    (by
    rw [cutRat_val, cutRat_val, map_add (f := _), map_sub, map_mul, map_one,
      GlobalTheory.HeisLineF.cAF_cAF σ (GlobalTheory.SplitDetCharF.sig_invol hB.cm), _root_.GlobalTheory.HeisLineF.cAF_incAF]
    rfl)
  rw [e1, map_mul, mul_assoc, e2, mul_one]
theorem real_data_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ
  JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hcm : s * mMF σ JS JT θ (g, h) = mMF σ JS JT θ (g, h) * s)
    (hd : (b ⊗ₖ aᵀ - 1).det ≠ 0) :
    Integrable (gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹))) volume ∧
      GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h)) ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧
      (∫ v, gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) v) * ∏ v, tauB B v (b ⊗ₖ aᵀ - 1).det =
        r * (-s).det * ((∏ v, tauB B v (b ⊗ₖ aᵀ).det) * GlobalTheory.RealWeil.dP s (mMF σ JS JT θ (g, h))) := by
  obtain ⟨q1, q2⟩ := det_mMF_k C ha hb
  have hH := GlobalTheory.T.hermitian_form_matrix_selfadjoint F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ
  have hU := GlobalTheory.T.archimedean_chart_gaussian_vector F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ θ
    C.inf ι C.chart (g⁻¹, h⁻¹)
  have c1 : s * mMF σ JS JT θ (g⁻¹, h⁻¹) = mMF σ JS JT θ (g⁻¹, h⁻¹) * s := by
    have := comm_inv (mMF σ JS JT θ) hcm
    rwa [Prod.inv_mk] at this
  have c2 : mMF σ JS JT θ (g⁻¹, h⁻¹) * mMF σ JS JT θ (g, h) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]
  have c3 : (mMF σ JS JT θ (g⁻¹, h⁻¹) - 1).det ≠ 0 := by
    rw [q2]
    exact Finset.prod_ne_zero_iff.2 fun v _ => (map_ne_zero _).2 hd
  rw [← q1, ← q2]
  exact _root_.PositivityTheory.ThKW.integral_gaussV_B hH.1 hs.sq hs.pos hU c1 c2 c3
theorem zF_rat_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (hε : ε * ε = ε) {g : GAF σ JS} {h : GAF σ
  JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (hΔ : (b ⊗ₖ aᵀ).det ≠ 0) :
    zF σ JS JT η ε hε (g, h) * η (cutRat ε hε (Units.mk0 _ hΔ)) = 1 := by
  have da := ha.det_ne C.hS
  have db := hb.det_ne C.hT
  have e1 := cutDet_rat C.hT hb ε hε
  rw [map_inv, inv_eq_iff_eq_inv] at e1
  have e2 := cutDet_rat C.hS ha ε hε
  have u0 : Units.mk0 _ hΔ = Units.mk0 _ db ^ nS * Units.mk0 _ da ^ nT := Units.ext (by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0, Units.val_mk0,
      Matrix.det_kronecker, Matrix.det_transpose, Fintype.card_fin, Fintype.card_fin])
  unfold zF
  rw [u0, e1, e2]
  simp only [MonoidHom.pow_apply, map_mul, map_pow, map_inv]
  generalize η (cutRat ε hε (Units.mk0 _ da)) = x
  generalize η (cutRat ε hε (Units.mk0 _ db)) = y
  rw [mul_comm (y ^ nS), mul_mul_mul_comm, inv_mul_cancel, inv_mul_cancel, one_mul]
theorem phase_rat_k (C : Ctx_k σ B JS JT ξ₀ θ ι) (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) {Δ d
  N : E} (hΔ : Δ ≠ 0) (hd : d ≠ 0)
    (hN : N ≠ 0) {m : ℕ} (d1 : Δ * σ Δ = 1) (d2 : Δ * σ d = (-1) ^ m * d) {z : Circle}
    (v0 : z * η (cutRat ε hε.idem (Units.mk0 _ hΔ)) = 1) :
    (z : ℂ) * η (cutRat _ (half_add_k C.good hε) (Units.mk0 _ hN * Units.mk0 _ hΔ)) =
      η (cutRat ε hε.idem ((-1) ^ m)) * η (cutRat _ (half_add_k C.good hε) (Units.mk0 _ hN
        * Units.mk0 _ hd)) := by
  rw [← Circle.coe_mul, ← Circle.coe_mul]
  have u1 : Units.mk0 _ hΔ * Units.map (σ : E →* E) (Units.mk0 _ hΔ) = 1 := Units.ext d1
  have u2 : Units.mk0 _ hΔ * Units.map (σ : E →* E) (Units.mk0 _ hd) = (-1) ^ m * Units.mk0 _ hd :=
    Units.ext (by simpa using d2)
  exact congrArg _ (GlobalTheory.RatAut.phase_identity (η.comp (cutRat ε hε.idem)) (η.comp (cutRat _
    (half_add_k C.good hε)))
    (Units.map (σ : E →* E)) (eta_cut_k C.good h2 hε) v0 u1 u2)
end
end
end PositivityTheory.ThKW
end
