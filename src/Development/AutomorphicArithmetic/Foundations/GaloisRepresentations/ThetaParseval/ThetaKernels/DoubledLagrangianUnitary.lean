module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledThetaLiftConvergence
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFinsetAnnLeK
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DCdE
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LamFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticTraceFormAlternatingSwap
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAdelicFourierSeparatingCharsVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainRationalMatricesTower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCMRealLineAddNoPhase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutProdA
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfoBis
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralMul
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.MapHaar
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.MfacInvMul
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.PrSingle
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ProjFacts

/-! # DoubledLagrangianUnitary: Consolidated global theta-kernel definitions and proofs (DoubledLagrangianUnitary). -/
@[expose] public section

open scoped TensorProduct Matrix
open GlobalTheory.LagrTheta (lagrInt)
open GlobalTheory.SWQ (rat)
open GlobalTheory.WeilSchrodinger.DblTargetF (dblG)
open UpperTheory.TP.W (GoodK)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section
open scoped TensorProduct Matrix Kronecker
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
set_option linter.unusedSectionVars false
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
theorem change_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B :
  Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ (s : GL (Fin nT) (AF F ⊗[F] E)) (N : WOF F E nS nT → ℂ), Continuous N → Integrable N ν →
      Continuous (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ∧
      Integrable (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ν ∧
      ∀ y : WOF F E nS nT, ∫ v, phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v ∂ν =
        ((mfac F E nS s : ℝ) : ℂ) ^ 2 * ∫ w, phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) ∂ν := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕 s N hN hI
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have hA : ∀ M M' : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), M * M' = 1 → (M'.map (cAF σ))ᵀ * (M.map (cAF σ))ᵀ = 1 :=
    fun M M' h => by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  let A : GL (Fin nT) (AF F ⊗[F] E) := ⟨(s.1.map (cAF σ))ᵀ, ((s⁻¹).1.map (cAF σ))ᵀ, hA _ _ s.inv_mul, hA _ _ s.mul_inv⟩
  let e : WOF F E nS nT ≃+ WOF F E nS nT :=
    { toFun := fun w => A.1 * w
      invFun := fun w => (A⁻¹).1 * w
      left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun v w => Matrix.mul_add _ v w }
  have c1 : Continuous e := continuous_const.matrix_mul continuous_id
  have c2 : Continuous e.symm := continuous_const.matrix_mul continuous_id
  refine ⟨hN.comp c1, ?_, fun y => ?_⟩
  · have : (ν.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map ν c1 c2
    obtain ⟨c, hc⟩ : ∃ c : NNReal, ν.map e = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩
    have h1 : Integrable N (ν.map e) := by
      rw [hc]
      exact hI.smul_measure_nnreal
    exact (integrable_map_measure hN.aestronglyMeasurable c1.measurable.aemeasurable).1 h1
  · have h := integral_mul ν hν A (fun v => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v)
    have hn : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det A) =
        Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det s) := by
      refine Units.ext (GlobalTheory.SplitDetCharF.tensor_inj (F := F) (E := E) ?_)
      have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (GlobalTheory.SplitDetCharF.sig_invol hB.cm x)
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
      have hd : A.1.det = cAF σ s.1.det := by
        show ((s.1.map (cAF σ))ᵀ).det = _
        rw [Matrix.det_transpose, RingHom.map_det]; rfl
      show algebraMap _ _ (Algebra.norm (AF F) A.1.det) = algebraMap _ _ (Algebra.norm (AF F) s.1.det)
      rw [GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, hd, hcc,
        mul_comm]
    rw [hn] at h
    set m : ℝ := (distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
      (Matrix.GeneralLinearGroup.det s)) : ℝ) with hm
    have hm0 : 0 < m := NNReal.coe_pos.2 distribHaarChar_pos
    have hf : mfac F E nS s ^ 2 = m ^ nS := by
      show (m ^ ((Fintype.card (Fin nS) : ℝ) / 2)) ^ 2 = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, Fintype.card_fin, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have h2 : (fun w : WOF F E nS nT => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) (A.1 * w) * N (A.1 * w)) =
        fun w => phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) := funext fun w => by
      rw [← phase_move JS JT hT.2 ξ₀ B.ψ s y w]
    rw [h2] at h
    rw [h, ← Complex.ofReal_pow, hf, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hm0 _).ne',
      Complex.ofReal_one, one_mul]
theorem unit_coef_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (dblG JT) (fun w : InfinitePlace F => (B.emb w).1) ξ₀
          B.ψ χS 1 ωd →
      ∀ (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))), μW.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW →
      ∀ (h : GAF σ (dblG JT)) (w₀ : WOF F E nS (nT + nT))
        (f : WOF F E nS (nT + nT) → ℂ),
        IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f →
        ∫ w in 𝓕W, heisOF σ JS (dblG JT) ξ₀ B.ψ (actOF σ JS
          (dblG JT) 1 h w₀) (ωd (1, h) f) w *
            starRingEnd ℂ (ωd (1, h) f w) ∂μW =
          ∫ w in 𝓕W,
            heisOF σ JS (dblG JT) ξ₀ B.ψ w₀ f w * starRingEnd ℂ (f w) ∂μW := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ χS ωd hω μ 𝓕 hμ h𝓕 h w₀ f hf
  rw [← hω.om_heis 1 h w₀ f hf]
  exact GlobalTheory.ThetaSchurF.scalar_eq hω.std.1.2.1 μ 𝓕 hμ h𝓕 (ωd (1, h)) (hω.om_pres _)
    (hω.om_unit μ 𝓕 hμ h𝓕 _) _ _
    (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ w₀ f hf) hf
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
section
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
  PositivityTheory.ThKW.PhaseFourierInjectivity PositivityTheory.ThKW.LagrangianProjectionFormula in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.finj_k : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ N₁ N₂ : WOF F E nS nT → ℂ, Continuous N₁ → Continuous N₂ → Integrable N₁ ν → Integrable N₂ ν →
      (∀ y, ∫ v, phase σ JS JT ξ₀ B.ψ y v * N₁ v ∂ν = ∫ v, phase σ JS JT ξ₀ B.ψ y v * N₂ v ∂ν) → N₁ = N₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 N₁ N₂ c₁ c₂ i₁ i₂ hN
  have hψ : IsStd B.ψ := hB.std
  have hψn : ∀ a, ‖B.ψ a‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hB.std
  have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z :=
    GlobalTheory.HeisLineF.cAF_cAF σ (GlobalTheory.SplitDetCharF.sig_invol hB.cm)
  have he : Continuous (vecE F E nS nT) := by
    show Continuous fun (w : WOF F E nS nT) (k : Fin (nT * nS)) => w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm
      k).2
    exact continuous_pi fun k => continuous_id.matrix_elem _ _
  have he' : Continuous (vecE F E nS nT).symm := by
    show Continuous fun (u : Fin (nT * nS) → AF F ⊗[F] E) =>
      ((fun i j => u (finProdFinEquiv (i, j))) : WOF F E nS nT)
    exact continuous_pi fun i => continuous_pi fun j => continuous_apply _
  have : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.isTopologicalAddGroup (AF F) (AF F ⊗[F] E)
  let E' : WOF F E nS nT ≃ₜ+ (Fin (nT * nS) → AF F ⊗[F] E) :=
    { toAddEquiv := vecE F E nS nT, continuous_toFun := he, continuous_invFun := he' }
  let : MeasurableSpace (Fin (nT * nS) → AF F ⊗[F] E) := borel _
  have : BorelSpace (Fin (nT * nS) → AF F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  let em : WOF F E nS nT ≃ᵐ (Fin (nT * nS) → AF F ⊗[F] E) := E'.toHomeomorph.toMeasurableEquiv
  have := hν
  have hμ : (ν.map em).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν E'
  have hpc : ∀ a : WOF F E nS nT, Continuous (pr σ JS ξ₀ a) := fun a => IsModuleTopology.continuous_of_linearMap _
  have hph : ∀ a, Continuous (phase σ JS JT ξ₀ B.ψ a) := by
    intro a
    have e : phase σ JS JT ξ₀ B.ψ a = fun v => B.ψ (pr σ JS ξ₀ a (vecE F E nS nT v)) :=
      funext fun v => phase_eq σ JS JT hT.2 ξ₀ B.ψ a v
    rw [e]
    exact hψ.1.comp ((hpc a).comp he)
  have hint : ∀ a (N : WOF F E nS nT → ℂ), Integrable N ν →
      Integrable (fun v => phase σ JS JT ξ₀ B.ψ a v * N v) ν := by
    intro a N hNi
    refine hNi.bdd_mul (c := 1) (hph a).aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    rw [phase_eq σ JS JT hT.2, hψn]
  set N : (Fin (nT * nS) → AF F ⊗[F] E) → ℂ := fun u => N₁ ((vecE F E nS nT).symm u) - N₂ ((vecE F E nS nT).symm u)
    with hNdef
  have hNc : Continuous N := (c₁.comp he').sub (c₂.comp he')
  have hNi : Integrable N (ν.map em) := by
    rw [integrable_map_equiv em N]
    have : N ∘ em = fun v => N₁ v - N₂ v := by
      funext v
      simp only [hNdef, Function.comp_apply]
      rw [show (vecE F E nS nT).symm (em v) = v from (vecE F E nS nT).symm_apply_apply v]
    rw [this]
    exact i₁.sub i₂
  have key : ∀ a, ∫ u, B.ψ (pr σ JS ξ₀ a u) * N u ∂(ν.map em) = 0 := by
    intro a
    rw [integral_map_equiv em]
    have hx : ∀ v, B.ψ (pr σ JS ξ₀ a (em v)) * N (em v) =
        phase σ JS JT ξ₀ B.ψ a v * N₁ v - phase σ JS JT ξ₀ B.ψ a v * N₂ v := by
      intro v
      have h1 : (vecE F E nS nT).symm (em v) = v := (vecE F E nS nT).symm_apply_apply v
      have h2 : em v = vecE F E nS nT v := rfl
      simp only [hNdef, h2, AddEquiv.symm_apply_apply]
      rw [phase_eq σ JS JT hT.2]
      ring
    simp_rw [hx]
    rw [integral_sub (hint a N₁ i₁) (hint a N₂ i₂), hN a, sub_self]
  have h0 := _root_.GlobalTheory.AdelicFourierUniq.eq_zero F E B.ψ hψ (nT * nS) (WOF F E nS nT) (pr σ
    JS ξ₀) (pr_add σ JS ξ₀)
    (fun u hu => pr_sep σ hcc hψ JS hS.2 ξ₀ hξ₀ u hu) (ν.map em) hμ N hNc hNi key
  funext v
  have := congrFun h0 (vecE F E nS nT v)
  simp only [hNdef, AddEquiv.symm_apply_apply, Pi.zero_apply] at this
  exact sub_eq_zero.1 this
end

noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
  GlobalTheory.ThetaTransform
theorem heis_C_k {σ : E →ₐ[F] E} {B : Base F E} (_hB : GoodK σ B) {nS nT : ℕ} (JS : Matrix (Fin
  nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (N : ℕ)
    (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N)
    (hCe : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u))
    (he : ∀ w w', symplOF σ JS (dblG JT) ξ₀ w w' = symV (e w) (e w'))
    (Φ : (Fin N → AF F) → ℂ) (y : WOF F E nS nT) :
    heisOF σ JS (dblG JT) ξ₀ B.ψ (dC (AF F ⊗[F] E) nT * y) (thV B.ψ Φ ∘ e) =
      thV B.ψ (fun x => B.ψ (x ⬝ᵥ β y) * Φ x) ∘ e := by
  have hCy : e (dC (AF F ⊗[F] E) nT * y) = (0, β y) := by
    have h := hCe y 0
    rw [Matrix.mul_zero, add_zero, map_zero] at h
    exact h
  have h2 : (⅟(2 : AF F)) = algebraMap F (AF F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  funext w
  simp only [Function.comp_apply, heisOF, thV, thetaSum, schr]
  rw [map_add (f := _), hCy]
  have hph : symplOHF σ JS (dblG JT) ξ₀ w (dC (AF F ⊗[F] E) nT * y) =
      ⅟(2 : AF F) * ((e w).1 ⬝ᵥ β y) := by
    rw [symplOHF, he, hCy, h2]
    simp [symV]
  rw [hph, ← tsum_mul_left]
  refine tsum_congr fun ξ => ?_
  set x₁ := (e w).1
  set y₁ := (e w).2
  set b := β y
  set r : Fin N → AF F := fun i => algebraMap F (AF F) (ξ i)
  have hw : e w = (x₁, y₁) := rfl
  simp only [hw, Prod.mk_add_mk, add_zero]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  have h22 : (⅟(2 : AF F)) + ⅟2 = 1 := invOf_two_add_invOf_two
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (x₁ ⬝ᵥ b) * h22
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
set_option linter.unusedSectionVars false
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
  PositivityTheory.ThKW.PhaseFourierInjectivity GlobalTheory.ThetaTransform GlobalTheory.RatDarboux
variable {σ : E →ₐ[F] E} {nS nT N : ℕ}
theorem pairing_k {B : Base F E} (hB : GoodK σ B) {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0) :
    ∃ (N : ℕ) (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (a b : Matrix (Fin nT) (Fin nS) E ≃ₗ[F] (Fin N → F)),
      (∀ v u,
        symplOF σ JS (dblG JT) ξ₀ (dCd F JT * v) (dC (AF F ⊗[F] E) nT * u) =
        α v ⬝ᵥ β u) ∧ (∀ x, α (ratWF x) = rat (a x)) ∧ ∀ x,
          β (ratWF x) = rat (b x) := by
  classical
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hinv := GlobalTheory.SplitDetCharF.sig_invol hB.cm
  have eB : (-1 : AF F ⊗[F] E) • incM F (-(ξ₀ • JS⁻¹)) = incM F (ξ₀ • JS⁻¹) := by
    funext i j
    simp [incM]
  have hbij := bijective_sympBil σ hinv (JA := (1 : Matrix (Fin nT) (Fin nT) E)ᵀ) (JB := -(ξ₀ • JS⁻¹)) (by simp)
    (by
      rw [← neg_smul, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 hξ)) (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hS.2)).ne_zero)
  let b := Module.finBasis F (Matrix (Fin nT) (Fin nS) E)
  let b' := b.dualBasis.map (LinearEquiv.ofBijective _ hbij).symm
  have hb : ∀ i j, symp σ (-1) (1 : Matrix (Fin nT) (Fin nT) E)ᵀ (-(ξ₀ • JS⁻¹)) (b' i) (b j) = if j = i then 1 else 0 :=
    fun i j => by
      have h1 := (LinearEquiv.ofBijective _ hbij).apply_symm_apply (b.dualBasis i)
      have h2 := LinearMap.congr_fun h1 (b j)
      rw [Module.Basis.dualBasis_apply_self] at h2
      exact h2
  let P : LinearMap.BilinForm (AF F) (WOF F E nS nT) :=
    sympBil (cA σ) (-1) (incM F (1 : Matrix (Fin nT) (Fin nT) E)ᵀ) (incM F (-(ξ₀ • JS⁻¹)))
  have hP : ∀ v u, P v u = (adB b').equivFun v ⬝ᵥ (adB b).equivFun u := fun v u => by
    have h0 : ∀ i j, P (adB b' i) (adB b j) = if j = i then 1 else 0 := fun i j => by
      rw [adB_apply, adB_apply]
      refine (symp_map (AF F) σ _ _ (b' i) (b j)).trans ?_
      rw [hb]
      split_ifs <;> simp
    conv_lhs => rw [← (adB b').sum_repr v, ← (adB b).sum_repr u]

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, h0, smul_eq_mul, mul_ite, mul_one,
      mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, dotProduct, Module.Basis.equivFun_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨_, (adB b').equivFun, (adB b).equivFun, b'.equivFun, b.equivFun, fun v u => ?_, adB_rat b', adB_rat b⟩
  rw [← hP]
  refine Eq.trans ?_ (GlobalTheory.TransportF.symplOF_eq_symp (JT := 1) rfl eB v u)
  unfold symplOF
  rw [hOF_dual JS JT hT.2, hOF_eq_trace, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
theorem coords_k {σ : E →ₐ[F] E} {B : Base F E} (hB : GoodK σ B) {nS nT : ℕ} {JS : Matrix (Fin
  nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0)
    (hσ : σ ξ₀ = -ξ₀) :
    ∃ (N : ℕ) (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F))
      (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N),
      (∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u)) ∧
      (∀ w w', symplOF σ JS (dblG JT) ξ₀ w w' = symV (e w) (e w')) ∧
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : Fin N → F,
        e (ratWF x) = (rat y, rat z)) ∧
      (∀ y z : Fin N → F, ∃ x : Matrix (Fin (nT + nT)) (Fin nS) E, e (ratWF x) = (rat y,
        rat z)) ∧
      Continuous e ∧ Continuous e.symm ∧
      Continuous α ∧ Continuous α.symm ∧ Continuous β ∧ Continuous β.symm ∧
      (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y : Fin N → F, β (ratWF x) = rat y) ∧
      (∀ y : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, β (ratWF x) = rat y) := by
  have hinv := GlobalTheory.SplitDetCharF.sig_invol hB.cm
  obtain ⟨N, α, β, a, b, hP, ha, hb⟩ := pairing_k hB hS hT hξ
  obtain ⟨d, U, V, hd, hd'⟩ := split (nS := nS) JT hT
  obtain ⟨e, he0⟩ : ∃ e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N, ∀ w, e w = (α (d w).1, β (d w).2) :=
    ⟨d.trans (α.prodCongr β), fun _ => rfl⟩
  have he : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u) := fun u v => by
    rw [he0, ← hd' (v, u), d.apply_symm_apply]
  have j1 : IsModuleTopology (AF F) (Fin N → AF F) := inferInstance
  have j2 : IsModuleTopology (AF F) (VA F N) := inferInstance
  have c1 := cont2 (modTop _ _) j2 e
  have c2 := cont2 (modTop _ _) j1 α
  have c3 := cont2 (modTop _ _) j1 β
  refine ⟨N, α, β, e, he, fun w w' => ?_, fun x => ?_, fun y z => ?_, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2,
    fun x => ⟨_, hb x⟩, fun y => ⟨b.symm y, by rw [hb, LinearEquiv.apply_symm_apply]⟩⟩
  · obtain ⟨⟨v, u⟩, rfl⟩ := d.symm.surjective w
    obtain ⟨⟨v', u'⟩, rfl⟩ := d.symm.surjective w'
    have s1 : symplOF σ JS (dblG JT) ξ₀ (dC (AF F ⊗[F] E) nT * u)
        (dC (AF F ⊗[F] E) nT * u') = 0 := by rw [symplOF, h_CC, mul_zero, map_zero]
    have s2 : symplOF σ JS (dblG JT) ξ₀ (dCd F JT * v) (dCd F JT * v') = 0 := by
      rw [symplOF, dCd_eq, Matrix.mul_assoc, Matrix.mul_assoc, h_AA, mul_zero, map_zero]
    have s3 := _root_.GlobalTheory.SymplSkew.symplOF_swap F E σ hinv _ _ JS _ hS
      (GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT) ξ₀ hσ
      (dCd F JT * v') (dC (AF F ⊗[F] E) nT * u)
    rw [hd', hd', he, he, GlobalTheory.ThetaSchurF.symplOF_add_left, GlobalTheory.ThetaSchurF.symplOF_add_right,
      GlobalTheory.ThetaSchurF.symplOF_add_right, s1, s2, s3, hP, hP, symV]
    ring
  · refine ⟨a (V * x), b (U * x), ?_⟩
    rw [he0, hd, rat_mul, rat_mul, ha, hb]
  · refine ⟨dC E nT * b.symm z + dCdE JT * a.symm y, ?_⟩
    have : (ratWF (dC E nT * b.symm z + dCdE JT * a.symm y) : WOF F E nS (nT + nT)) =
        dC (AF F ⊗[F] E) nT * (ratWF (b.symm z) : WOF F E nS nT) + dCd F JT * (ratWF (a.symm y) : WOF F E nS nT) := by
      rw [← dC_map (incAF F E), dCd, rat_mul, rat_mul]
      exact Matrix.map_add _ (map_add _) _ _
    rw [this, he, ha, hb, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
  GlobalTheory.ThetaTransform
theorem lam_formula_k {σ : E →ₐ[F] E} {B : Base F E} (hB : GoodK σ B) {nS nT : ℕ} (JS : Matrix
  (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (hν : ν.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) (N : ℕ)
    (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N)
    (hCe : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u))
    (he : ∀ w w', symplOF σ JS (dblG JT) ξ₀ w w' = symV (e w) (e w'))
    (hβc : Continuous β) (_hβs : Continuous β.symm)
    (hr1 : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y : Fin N → F, β (ratWF x) = rat y)
    (_hr2 : ∀ y : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, β (ratWF x) = rat y) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F (Fin N), ∀ v : WOF F E nS nT,
      lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
        (heisOF σ JS (dblG JT) ξ₀ B.ψ (dCd F JT * v) (thV B.ψ Φ ∘ e)) =
        c * Φ (α v) := by
  classical
  obtain ⟨i1, i2, i3, i4, i5, K, hK,
    hKc⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have := i1
  have := i2
  have := i3
  have := i4
  have := i5
  have hBor : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have : Countable E := GlobalTheory.ThetaParsevalInner.countable_numberField E
  have : Countable F := GlobalTheory.ThetaParsevalInner.countable_numberField F
  have : Countable (ratLF F E nS nT) := by
    refine Function.Surjective.countable
      (f := fun m : Fin nT → Fin nS → E => (⟨(incAF F E).toAddMonoidHom.mapMatrix (Matrix.of m),
        AddMonoidHom.mem_range.2 ⟨_, rfl⟩⟩ : ratLF F E nS nT)) ?_
    rintro ⟨r, m, rfl⟩
    exact ⟨m, rfl⟩
  obtain ⟨Nn,
    hNn⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WOF F E nS nT) (ratLF F E nS nT) K hK hKc).2
    (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
  obtain ⟨h0, htop, -, -⟩ := hNn ν 𝓕 hν h𝓕
  have : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.mpr htop
  have := hν
  have hstd := GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hstd.1
  refine ⟨((ν 𝓕).toReal : ℂ), ?_, fun Φ hΦ v => ?_⟩
  · exact_mod_cast (ENNReal.toReal_pos h0 htop).ne'
  set x : Fin N → AF F := α v with hx
  obtain ⟨emb, hemb⟩ : ∃ emb : (Fin N → F) → (Fin N → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (Fin N → F) → ℂ, a = fun ξ => Φ (emb ξ + x) := ⟨_, rfl⟩
  obtain ⟨ch, hch⟩ : ∃ ch : (Fin N → F) → WOF F E nS nT → ℂ, ch = fun ξ u => B.ψ (emb ξ ⬝ᵥ β u) := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    subst ha hemb
    exact h0
  have hch_norm : ∀ ξ u, ‖ch ξ u‖ = 1 := fun ξ u => by rw [hch]; exact hnorm _
  have hch_cont : ∀ ξ, Continuous (ch ξ) := fun ξ => by
    rw [hch]; exact hcont.comp (continuous_const.dotProduct hβc)
  have hint : ∀ u : WOF F E nS nT,
      heisOF σ JS (dblG JT) ξ₀ B.ψ (dCd F JT * v) (thV B.ψ Φ ∘ e)
        (dC (AF F ⊗[F] E) nT * u) = ∑' ξ, a ξ * ch ξ u := by
    intro u
    have h1 : e (dC (AF F ⊗[F] E) nT * u) = (0, β u) := by
      have := hCe u 0
      rwa [Matrix.mul_zero, add_zero, map_zero] at this
    have h2 : e (dCd F JT * v) = (α v, 0) := by
      have := hCe 0 v
      rwa [Matrix.mul_zero, zero_add, map_zero] at this
    simp only [heisOF, symplOHF, Function.comp_apply, he, h1, h2, hCe, GlobalTheory.ThetaOntoF.algebraMap_half]
    unfold thV thetaSum schr
    rw [← tsum_mul_left]
    congr 1; funext ξ
    subst ha hch hemb
    simp only [symV, dotProduct_zero, zero_sub]
    exact psi_cancel B.ψ _ _ _
  have hFint : ∀ ξ, Integrable (fun u => a ξ * ch ξ u) (ν.restrict 𝓕) := fun ξ =>
    (Integrable.of_bound (hch_cont _).aestronglyMeasurable 1 (ae_of_all _ fun u => (hch_norm _ _).le)).const_mul _
  have hnormint : ∀ ξ, ∫ u in 𝓕, ‖a ξ * ch ξ u‖ ∂ν = ‖a ξ‖ * ν.real 𝓕 := by
    intro ξ
    simp only [norm_mul, hch_norm, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun ξ => ∫ u in 𝓕, ‖a ξ * ch ξ u‖ ∂ν := by
    simp_rw [hnormint]
    exact hsum.mul_right _
  have horth : ∀ ζ : Fin N → F, ∫ u in 𝓕, ch ζ u ∂ν = if ζ = 0 then (ν.real 𝓕 : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ u, ch 0 u = 1 := fun u => by simp [hch, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push Not at h; exact hζ (funext h)
      refine GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist ν (ratLF F E nS nT) h𝓕 (h := ch ζ) ?_
        (c := β.symm (Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0))) (a := B.ψ s0) ?_ hs0
      · intro r hr u
        obtain ⟨x₀, rfl⟩ := hr
        obtain ⟨η, hη⟩ := hr1 x₀
        have hr' : β ((incAF F E).toAddMonoidHom.mapMatrix x₀) = rat η := hη
        simp only [hch, map_add (f := _), hr', dotProduct_add, AddChar.map_add_eq_mul]

        rw [show emb ζ ⬝ᵥ rat η = algebraMap F (AF F) (ζ ⬝ᵥ η) by
        subst hemb; simp [dotProduct, map_sum, map_mul, rat], htriv, one_mul]
      · intro u
        simp only [hch, map_add (f := _), LinearEquiv.apply_symm_apply, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  unfold lagrInt
  simp_rw [hint]
  rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
  simp_rw [integral_const_mul, horth]
  rw [tsum_eq_single 0 (fun ξ hξ => by rw [ite_eq_right hξ, mul_zero]), ite_eq_left rfl, ha, hemb]
  have hz : (fun i : Fin N => (0 : AF F)) + x = x := by funext i; simp
  simp only [Pi.zero_apply, map_zero]
  rw [hz, Measure.real]
  ring
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end

abbrev _root_.GlobalTheory.T.doubled_lagrangian_unitary :=
  GlobalTheory.ThetaLevelF.thetaTr_levelF_k

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
  GlobalTheory.ThetaTransform
open scoped Pointwise in
theorem parseval_pol_k {σ : E →ₐ[F] E} {B : Base F E} (hB : GoodK σ B) {nS nT : ℕ} (N : ℕ)
    (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N) (hec : Continuous e) (hes : Continuous e.symm)
    (hrat : ∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : Fin N → F,
        e (ratWF x) = (rat y, rat z))
    (hrat' : ∀ y z : Fin N → F, ∃ x : Matrix (Fin (nT + nT)) (Fin nS) E, e (ratWF x) = (rat y,
      rat z)) :
    ∃ (μN : Measure (Fin N → AF F)) (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))) (c : ℝ),
      μN.IsAddHaarMeasure ∧ μW.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW ∧ 0 < c ∧
      ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
        ∫ w in 𝓕W, thV B.ψ Φ₁ (e w) * starRingEnd ℂ (thV B.ψ Φ₂ (e w)) ∂μW =
          (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μN := by
  obtain ⟨μW, 𝓕W, hμW, h𝓕W⟩ := GlobalTheory.TowerFD.exists_fd_any F E nS (nT + nT)
  obtain ⟨i1, i2, -, -, -, -⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS (nT + nT)
  have := i1
  have := i2
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have : BorelSpace (AF F) := ⟨rfl⟩
  have hb : (MeasurableSpace.pi : MeasurableSpace (Fin N → AF F)) = borel _ := BorelSpace.measurable_eq
  let mP : MeasurableSpace (VA F N) := borel _
  have : BorelSpace (VA F N) := ⟨rfl⟩
  have : BorelSpace (WOF F E nS (nT + nT)) := ⟨rfl⟩
  let ca : WOF F E nS (nT + nT) ≃ₜ+ VA F N :=
    { e.toAddEquiv with continuous_toFun := hec, continuous_invFun := hes }
  let me : WOF F E nS (nT + nT) ≃ᵐ VA F N := ca.toHomeomorph.toMeasurableEquiv
  have hme : ∀ w, me w = e w := fun _ => rfl
  have into : ∀ g ∈ ratLF F E nS (nT + nT), e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N), e.symm p ∈ ratLF F E nS (nT + nT) := by
    intro p hp
    obtain ⟨y, z, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
    obtain ⟨x, hx⟩ := hrat' y z
    have : e.symm (rat y, rat z) = ratWF x := by rw [← hx]; exact e.symm_apply_apply _
    rw [show ((fun i => algebraMap F (AF F) (y i)), fun i => algebraMap F (AF F) (z i)) =
      (rat y, rat z) from rfl, this]
    exact ⟨x, rfl⟩
  have hν : (μW.map me).IsAddHaarMeasure := ca.isAddHaarMeasure_map μW
  have h𝓕 : IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (me '' 𝓕W) (μW.map me) := by
    refine ⟨?_, ?_, ?_⟩
    · have hqmp : QuasiMeasurePreserving me.symm (μW.map me) μW :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕W = me.symm ⁻¹' 𝓕W :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕W.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕W.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show e ((g : WOF F E nS (nT + nT)) + x) = e g + e x
      rw [map_add (f := _)]
    · intro p q hpq
      let g : ratLF F E nS (nT + nT) := ⟨e.symm p, onto' p p.2⟩
      let h : ratLF F E nS (nT + nT) := ⟨e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro eq
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratLF F E nS (nT + nT) => e (t : WOF F E nS (nT + nT))) eq
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (k : ratLF F E nS (nT + nT)),
          (k : WOF F E nS (nT + nT)) = e.symm r → r +ᵥ me '' 𝓕W = me '' (k +ᵥ 𝓕W) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : VA F N) + e w = e ((k : WOF F E nS (nT + nT)) + w)
        rw [map_add (f := _), hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (μW.map me) (p +ᵥ me '' 𝓕W) (q +ᵥ me '' 𝓕W)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕W.aedisjoint hgh
  have key : ∀ m : MeasurableSpace (Fin N → AF F), m = borel _ →
      ∃ (μ : @Measure _ m) (c : ℝ), @Measure.IsAddHaarMeasure _ _ _ m μ ∧ 0 < c ∧
        ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
          ∫ w in me '' 𝓕W, thV B.ψ Φ₁ w * starRingEnd ℂ (thV B.ψ Φ₂ w) ∂(μW.map me) =
            (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μ := by
    rintro m rfl
    exact ParsevalPolarization.parseval_rational_pairing hB N (μW.map me) hν (me '' 𝓕W) h𝓕
  obtain ⟨μN, c, hμN, hc, hK⟩ := key _ hb
  refine ⟨μN, μW, 𝓕W, c, hμN, hμW, h𝓕W, hc, fun Φ₁ hΦ₁ Φ₂ hΦ₂ => ?_⟩
  rw [← hK Φ₁ hΦ₁ Φ₂ hΦ₂, MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, integral_map_equiv]
  rfl
end PositivityTheory.ThKW.AdelicSchwartzProperties
end

noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
  PositivityTheory.ThKW.LagrangianIntegralFactorisation GlobalTheory.ThetaTransform
theorem coef_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B :
  Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∃ (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))) (κ : ℝ), μW.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW ∧ 0 < κ ∧
      ∀ f, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f →
        Continuous (nrm σ JS JT ξ₀ B.ψ ν 𝓕 f) ∧ Integrable (nrm σ JS JT ξ₀ B.ψ ν 𝓕 f) ν ∧
        ∀ y : WOF F E nS nT,
          ∫ w in 𝓕W,
            heisOF σ JS (dblG JT) ξ₀ B.ψ (dC (AF F ⊗[F] E) nT * y) f w *
            starRingEnd ℂ (f w) ∂μW =
            (κ : ℂ) * ∫ v, phase σ JS JT ξ₀ B.ψ y v * nrm σ JS JT ξ₀ B.ψ ν 𝓕 f v ∂ν := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕
  have hT' := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT
  have hstd := GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB
  obtain ⟨N, α, β, e, hCe, he, hrat, hrat', hec, hes, hαc, hαs, hβc, hβs, hr1,
    hr2⟩ := AdelicSchwartzProperties.coords_k hB hS hT hξ hσ
  obtain ⟨μN, μW, 𝓕W, c₁, hμN, hμW, h𝓕W, hc₁,
    hpar⟩ := AdelicSchwartzProperties.parseval_pol_k hB N e hec hes hrat hrat'
  obtain ⟨c₀, hc₀,
    hlam⟩ := AdelicSchwartzProperties.lam_formula_k hB JS JT ξ₀ ν 𝓕 hν h𝓕 N α β e hCe he
    hβc hβs hr1 hr2
  obtain ⟨c₂, hc₂, hmap, hint⟩ := AdelicSchwartzProperties.map_haar α hαc hαs ν hν μN hμN
  have hn0 := norm_pos_iff.2 hc₀
  refine ⟨μW, 𝓕W, c₁ / (c₂ * ‖c₀‖ ^ 2), hμW, h𝓕W, by positivity, fun f hf => ?_⟩
  obtain ⟨Φ, hΦ,
    rfl⟩ := GlobalTheory.ThetaOntoF.exists_thV_eqF_k F E σ B hB nS (nT + nT) JS _ hS hT' ξ₀ hξ hσ hstd N e he
    hrat f hf
  obtain ⟨hΦc, hΦi, hΦm⟩ := AdelicSchwartzProperties.schA_facts_k hB N μN hμN Φ hΦ
  have hnrm : nrm σ JS JT ξ₀ B.ψ ν 𝓕 (thV B.ψ Φ ∘ e) =
      fun v => ((‖c₀‖ ^ 2 : ℝ) : ℂ) * (Φ (α v) * starRingEnd ℂ (Φ (α v))) := by
    funext v
    unfold nrm
    rw [hlam Φ hΦ v, map_mul, Complex.ofReal_pow, ← Complex.mul_conj' c₀]
    ring
  have hph : ∀ y v, phase σ JS JT ξ₀ B.ψ y v = B.ψ (α v ⬝ᵥ β y) := by
    intro y v
    unfold phase
    rw [he]
    have h1 : e (dCd F JT * v) = (α v, 0) := by
      have := hCe 0 v
      rwa [Matrix.mul_zero, zero_add, map_zero] at this
    have h2 : e (dC (AF F ⊗[F] E) nT * y) = (0, β y) := by
      have := hCe y 0
      rwa [Matrix.mul_zero, add_zero, map_zero] at this
    rw [h1, h2]
    simp [symV]
  refine ⟨?_, ?_, fun y => ?_⟩
  · rw [hnrm]
    exact continuous_const.mul ((hΦc.comp hαc).mul (Complex.continuous_conj.comp (hΦc.comp hαc)))
  · rw [hnrm]
    exact ((hint _).2 hΦi).const_mul _
  · rw [AdelicSchwartzProperties.heis_C_k hB JS JT ξ₀ N α β e hCe he Φ y]
    have hl : ∫ w in 𝓕W, (thV B.ψ (fun x => B.ψ (x ⬝ᵥ β y) * Φ x) ∘ e) w * starRingEnd ℂ ((thV B.ψ Φ ∘ e) w) ∂μW =
        (c₁ : ℂ) * ∫ x, B.ψ (x ⬝ᵥ β y) * Φ x * starRingEnd ℂ (Φ x) ∂μN :=
      hpar _ (hΦm (β y)) Φ hΦ
    rw [hl, hnrm]
    simp_rw [hph]
    have hr : ∫ v, B.ψ (α v ⬝ᵥ β y) * (((‖c₀‖ ^ 2 : ℝ) : ℂ) * (Φ (α v) * starRingEnd ℂ (Φ (α v)))) ∂ν =
        ((‖c₀‖ ^ 2 : ℝ) : ℂ) * ((c₂ : ℂ) * ∫ x, B.ψ (x ⬝ᵥ β y) * Φ x * starRingEnd ℂ (Φ x) ∂μN) := by
      rw [← hmap (fun x => B.ψ (x ⬝ᵥ β y) * Φ x * starRingEnd ℂ (Φ x)), ← integral_const_mul]
      congr 1; funext v
      ring
    rw [hr]
    have hc2 : (c₂ : ℂ) ≠ 0 := by exact_mod_cast hc₂.ne'
    have hc0 : ((‖c₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hn0 2).ne'
    have hn' : ((‖c₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    push_cast
    field_simp
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation
  PositivityTheory.ThKW.NormModulusHeisenberg in
theorem PositivityTheory.ThKW.PhaseFourierInjectivity.norm_law_k : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ (h : GAF σ (dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
        mtF σ (dblG JT) h * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 →
      ∀ f, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f →
        ‖lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f)‖ =
          mfac F E nS t * ‖lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t hht f hf
  obtain ⟨μW, 𝓕W, κ, hμW, h𝓕W, hκ,
    hcoef⟩ := PositivityTheory.ThKW.PhaseFourierInjectivity.coef_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν
    h𝓕
  have hωf := hωd.om_pres (1, h) f hf
  obtain ⟨c1, i1, e1⟩ := hcoef _ hωf
  obtain ⟨c0, i0, e0⟩ := hcoef f hf
  obtain ⟨cL, iL,
    eL⟩ := PositivityTheory.ThKW.PhaseFourierInjectivity.change_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν
    h𝓕 t _ c0 i0
  have hκ0 := Complex.ofReal_ne_zero.2 hκ.ne'
  have key : nrm σ JS JT ξ₀ B.ψ ν 𝓕 (ωd (1, h) f) = fun w =>
      ((mfac F E nS t : ℝ) : ℂ) ^ 2 * nrm σ JS JT ξ₀ B.ψ ν 𝓕 f ((t.1.map (cAF σ))ᵀ * w) := by
    refine PositivityTheory.ThKW.PhaseFourierInjectivity.finj_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕
      _ _ c1 (continuous_const.mul cL) i1
      (iL.const_mul _) fun y => ?_
    have hact : actOF σ JS (dblG JT) 1 h (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * y)) =
      dC (AF F ⊗[F] E) nT * y := by
      unfold actOF
      rw [inv_one, show mtF σ JS 1 = 1 by unfold mtF; rw [map_one, Units.val_one], Matrix.mul_one,
        ← Matrix.mul_assoc, hht, Matrix.mul_assoc, ← Matrix.mul_assoc t.1, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.one_mul]
    have u := PositivityTheory.ThKW.PhaseFourierInjectivity.unit_coef_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ χS
      ωd hωd μW 𝓕W hμW h𝓕W h
      (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * y)) f hf
    rw [hact, e1 y, e0 ((t⁻¹).1 * y), eL y] at u
    have u' := mul_left_cancel₀ hκ0 u
    rw [u', ← integral_const_mul]
    congr 1; funext w
    ring
  have k0 := congrFun key 0
  rw [Matrix.mul_zero, nrm_zero, nrm_zero] at k0
  have k1 : ‖lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f)‖ ^ 2 =
      (mfac F E nS t * ‖lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f‖) ^ 2 := by
    rw [mul_pow]
    exact_mod_cast k0
  exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (mfac_pos' nS t).le (norm_nonneg _)) two_ne_zero).1 k1
end
end
