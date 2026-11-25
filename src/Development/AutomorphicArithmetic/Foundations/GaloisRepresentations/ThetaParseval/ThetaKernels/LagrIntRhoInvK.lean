module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedEqDiagonalLagrangianThetaIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagLagrangian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaReNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensDiagEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralNeZeroOfCocompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixMemSpanIncM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvari
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousTransportFApplyK
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.InvHerm
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Mfac
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramHspOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

/-! # LagrIntRhoInvK: Consolidated global theta-kernel definitions and proofs (LagrIntRhoInvK). -/
@[expose] public section

open GlobalTheory.WeilSchrodinger (thetaTr)
open GlobalTheory.WeilSchrodinger.DblTargetF (dblG)
open UpperTheory.TP.W (GoodK)
open scoped TensorProduct Matrix
open scoped Matrix TensorProduct
open GlobalTheory.WeilM (schA)

section
open scoped Classical TensorProduct Matrix
open GlobalTheory.ThetaTrCont NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.LagrThetaAdm
open GlobalTheory.WeilSchrodinger
theorem exists_admissible_eq_lagrangian_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS)
      E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∃ l₂ ∈ (adeleClass F).adm κ, ∀ Φ ∈ schA F κ, l₂ Φ = GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) :
        Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)
        (thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hrat ν 𝓕 hν h𝓕
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  set Cm :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id with hCm
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hfin :=
    GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕
  have : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have : IsModuleTopology (AF F) (Matrix (Fin (nT + nT)) (Fin nS) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin (nT + nT) → Fin nS → AE F E))
  have hce : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hCu : Continuous fun u : WOF F E nS nT => Cm * u := continuous_const.matrix_mul continuous_id
  have hcont : ∀ Φ ∈ schA F κ, Continuous fun u : WOF F E nS nT => thetaTr F co B.ψ Φ (Cm * u) :=
    fun Φ hΦ => ((schA_cont F B.ψ hψ.1 hψ.2.1 hΦ).2.comp hce).comp hCu
  have hint : ∀ Φ ∈ schA F κ, Integrable (fun u => thetaTr F co B.ψ Φ (Cm * u)) (ν.restrict 𝓕) := fun Φ hΦ => by
    obtain ⟨C, hC⟩ := thetaSum_schA_bdd F B.ψ hψ.1 hψ.2.1 hΦ
    exact Integrable.of_bound (hcont Φ hΦ).aestronglyMeasurable C (Filter.Eventually.of_forall fun u => hC _)
  have hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, ∀ w,
      thetaTr F co B.ψ (Φ + Ψ) w = thetaTr F co B.ψ Φ w + thetaTr F co B.ψ Ψ w := by
    intro Φ hΦ Ψ hΨ w
    have e : schr B.ψ (co.e w) (Φ + Ψ) = schr B.ψ (co.e w) Φ + schr B.ψ (co.e w) Ψ :=
      funext fun x => by simp [schr, mul_add]
    show thetaSum F (schr B.ψ (co.e w) (Φ + Ψ)) = thetaSum F (schr B.ψ (co.e w) Φ) + thetaSum F (schr B.ψ (co.e w) Ψ)
    rw [e]
    exact ((schA_cont F B.ψ hψ.1 hψ.2.1 hΦ).1 _).tsum_add ((schA_cont F B.ψ hψ.1 hψ.2.1 hΨ).1 _)
  have hsmul : ∀ (a : ℂ) (Φ : (κ → AF F) → ℂ) w, thetaTr F co B.ψ (a • Φ) w = a * thetaTr F co B.ψ Φ w := by
    intro a Φ w
    have e : schr B.ψ (co.e w) (a • Φ) = a • schr B.ψ (co.e w) Φ := funext fun x => by
      simp only [schr, Pi.smul_apply, smul_eq_mul]
      ring
    show thetaSum F (schr B.ψ (co.e w) (a • Φ)) = a * thetaSum F (schr B.ψ (co.e w) Φ)
    rw [e, thetaSum_smul]
  let L : schA F κ →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => GlobalTheory.LagrTheta.lagrInt ν 𝓕 Cm (thetaTr F co B.ψ Φ)
      map_add' := fun Φ Ψ => by
        show ∫ u in 𝓕, thetaTr F co B.ψ (Φ.1 + Ψ.1) (Cm * u) ∂ν =
          ∫ u in 𝓕, thetaTr F co B.ψ Φ.1 (Cm * u) ∂ν + ∫ u in 𝓕, thetaTr F co B.ψ Ψ.1 (Cm * u) ∂ν
        simp_rw [hadd Φ.1 Φ.2 Ψ.1 Ψ.2]
        exact integral_add (hint _ Φ.2) (hint _ Ψ.2)
      map_smul' := fun a Φ => by
        show ∫ u in 𝓕, thetaTr F co B.ψ (a • Φ.1) (Cm * u) ∂ν = a • ∫ u in 𝓕, thetaTr F co B.ψ Φ.1 (Cm * u) ∂ν
        simp_rw [hsmul]
        rw [integral_const_mul, smul_eq_mul] }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend L
  have hlL : ∀ Φ (hΦ : Φ ∈ schA F κ), l Φ = L ⟨Φ, hΦ⟩ := fun Φ hΦ => LinearMap.congr_fun hl ⟨Φ, hΦ⟩
  refine ⟨l, ?_, fun Φ hΦ => hlL Φ hΦ⟩
  intro g hg
  obtain ⟨k, c, hc, hb⟩ := thetaSum_pure_le F B.ψ hψ.2.1 hg
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ := fun f =>
    Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hsn : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f =
        ((Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
    intro f
    rw [Seminorm.finset_sup_apply, Seminorm.finset_sup_apply]
    congr 2
    funext i
    simp [schwartzSeminormFamily, SchwartzMap.seminorm_apply]
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => L ⟨pureA F f g, hmem f⟩)
    (fun f f' => ?_) (fun a f => ?_) ⟨Finset.Iic (k, 0), c * ν.real 𝓕, mul_nonneg hc measureReal_nonneg, fun f => ?_⟩,
    fun f => ?_⟩
  · rw [← map_add (f := _)]
    congr 1
    exact Subtype.ext (funext fun x => by simp [pureA, add_mul])
  · rw [RingHom.id_apply, ← map_smul]
    congr 1
    exact Subtype.ext (funext fun x => by simp [pureA, mul_assoc])
  · show ‖∫ u in 𝓕, thetaTr F co B.ψ (pureA F f g) (Cm * u) ∂ν‖ ≤ _
    refine (norm_setIntegral_le_of_norm_le_const hfin fun u _ => hb f (co.e (Cm * u))).trans (le_of_eq ?_)
    rw [hsn]
    ring
  · exact hlL _ (hmem f)
end GlobalTheory.LagrThetaAdm
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
open GlobalTheory.LagrTheta (lagrInt)
noncomputable section
open scoped Pointwise in
open GlobalTheory.LagrThetaInv in
theorem GlobalTheory.LagrThetaInv.lagrInt_rho_inv_k : ∀ (F E :
  Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS)
      E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ,
        lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F]
          E)).submatrix finSumFinEquiv.symm id) (thetaTr F co B.ψ (co.rho B.ψ (((diagCols
          (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ)) =
          lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F]
          E)).submatrix finSumFinEquiv.symm id) (thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 _ h𝓕 u φ hφ
  change lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
      (thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)) =
    lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (thetaTr F co B.ψ φ)
  set g : WOF F E nS nT → ℂ := fun v => thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * v)
    with hg
  have h1 : ∀ v : WOF F E nS nT, thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)
      (dC (AF F ⊗[F] E) nT * v) = g (v + u) := by
    intro v
    simp only [hg, thetaTr, Darboux.rho]
    rw [schr_dC]
  have h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v := by
    rintro ⟨r, γ, rfl⟩ v
    obtain ⟨y, z, hyz⟩ := hco (dC E nT * γ)
    have hr : ((incAF F E).toAddMonoidHom.mapMatrix γ : WOF F E nS nT) = γ.map (incAF F E) := rfl
    show thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * (_ + v)) = _
    simp only [hg, thetaTr, Darboux.rho]
    rw [← schr_dC, hr, dC_mul_rat, hyz, GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ hB.std.2.1 y z]
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  have : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  have : MeasurableAdd (WOF F E nS nT) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  have : MeasurableConstVAdd (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun r => (continuous_const_add (r : WOF F E nS nT)).measurable⟩
  have : VAddInvariantMeasure (ratLF F E nS nT) (WOF F E nS nT) ν :=
    ⟨fun r s _ => measure_preimage_add ν (r : WOF F E nS nT) s⟩
  have : VAddCommClass (WOF F E nS nT) (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun a r x => add_left_comm a (r : WOF F E nS nT) x⟩
  have : Countable (ratLF F E nS nT) := by
    have : Countable E := by
      have : FiniteDimensional ℚ E := inferInstance
      exact ((Module.finBasis ℚ E).equivFun).injective.countable
    have : Countable (Matrix (Fin nT) (Fin nS) E) := inferInstanceAs (Countable (Fin nT → Fin nS → E))
    exact (Set.countable_range ((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS))).to_subtype
  unfold lagrInt
  simp_rw [h1]
  rw [← (measurePreserving_add_right ν u).setIntegral_image_emb (measurableEmbedding_addRight u) g 𝓕]
  have hF' : IsAddFundamentalDomain (ratLF F E nS nT) ((· + u) '' 𝓕) ν := by
    have hs : (· + u) '' 𝓕 = ((u : WOF F E nS nT) +ᵥ 𝓕 : Set (WOF F E nS nT)) := by
      rw [← Set.image_vadd]
      congr 1; funext v
      exact add_comm v u
    rw [hs]
    exact h𝓕.vadd_of_comm (G' := WOF F E nS nT) (u : WOF F E nS nT)
  exact hF'.setIntegral_eq h𝓕 h2
end
end

section
namespace GlobalTheory.LagrUniq
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  Formalism.IndefR.DatumF
theorem exists_lagrInt_ne_zero_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ :
  E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS)
      E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∃ φ ∈ schA F κ, GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F
        ⊗[F] E)).submatrix finSumFinEquiv.symm id) (thetaTr F co B.ψ φ) ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 hν h𝓕
  have hstd := hB.std
  have : IsModuleTopology (AF F) (WOF F E nS nT) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  set C :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id with hC
  set C₀ :=
    (diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) E).submatrix finSumFinEquiv.symm id with hC₀
  have hCC : C = incM F C₀ := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    rcases i with i | i <;> by_cases h : i = j <;>
      simp only [hC, hC₀, incM, diagCols, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply, id,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.one_apply, h, ite_true, ite_false, map_one,
          map_zero]
  let mC : WOF F E nS nT →ₗ[AF F] Matrix (Fin (nT + nT)) (Fin nS) (AF F ⊗[F] E) :=
    { toFun := fun u => C * u
      map_add' := fun u v => Matrix.mul_add _ _ _
      map_smul' := fun t u => Matrix.mul_smul _ _ _ }
  let Lm := co.e.toLinearMap ∘ₗ mC
  have hLm : ∀ u, Lm u = co.e (C * u) := fun u => rfl
  let S := LinearMap.range Lm
  have hiso : ∀ s ∈ S, ∀ s' ∈ S, s.1 ⬝ᵥ s'.2 = s'.1 ⬝ᵥ s.2 := by
    rintro _ ⟨u, rfl⟩ _ ⟨u', rfl⟩
    have h := co.form (C * u) (C * u')
    rw [GlobalTheory.WeilDiagIso.symp_diag_eq_zero F E σ nS nT JT JB ξ u u'] at h
    rw [hLm, hLm]
    exact (sub_eq_zero.mp h.symm)
  have hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
      Lm (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
    intro x
    have e : C * incM F x = incM F (C₀ * x) := by
      rw [hCC]
      simp only [incM]
      exact (Matrix.map_mul (f := (inclR (AF F) : E →+* AF F ⊗[F] E))).symm
    obtain ⟨y, z, h⟩ := hco (C₀ * x)
    exact ⟨y, z, by rw [hLm, e, h]⟩
  have hspan : S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} := by
    rintro _ ⟨u, rfl⟩
    have hu := Submodule.mem_map_of_mem (f := Lm) (GlobalTheory.matrix_mem_span_incM F E nT nS u)
    rw [Submodule.map_span] at hu
    refine Submodule.span_mono ?_ hu
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨⟨incM F x, rfl⟩, y, z, h⟩
  obtain ⟨Φ, hΦ, hcont, hre, hre0⟩ := GlobalTheory.ThetaPosIso.exists_theta_re_nonneg F B.ψ hstd κ S hiso hspan
  refine ⟨Φ, hΦ, ?_⟩
  have hI : ∀ u : WOF F E nS nT, thetaTr F co B.ψ Φ (C * u) = thetaSum F (schr B.ψ (Lm u)
    Φ) :=
    fun u => rfl
  show ∫ u in 𝓕, thetaTr F co B.ψ Φ (C * u) ∂ν ≠ 0
  simp_rw [hI]
  refine GlobalTheory.PeriodicPositiveIntegral.integral_ne_zero F E nS nT (fun u =>
    thetaSum F (schr B.ψ (Lm u) Φ)) ?_ ?_ ?_ ?_ ν 𝓕 hν h𝓕
  · exact hcont.comp (IsModuleTopology.continuous_of_linearMap Lm)
  · rintro _ ⟨γ₀, rfl⟩ u
    obtain ⟨y, z, h⟩ := hrat γ₀
    have e1 : Lm (((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS)) γ₀ + u) = Lm (incM F γ₀) + Lm u :=
      by
      rw [map_add (f := _)]; rfl
    have hr : Lm (incM F γ₀) ∈ S := ⟨incM F γ₀, rfl⟩
    have hw : Lm u ∈ S := ⟨u, rfl⟩
    have hi := hiso _ hw _ hr
    rw [h] at hi
    show thetaSum F (schr B.ψ (Lm (_ + u)) Φ) = _
    rw [e1, h, GlobalTheory.ThetaRatInv.thetaSum_schr_rat_add B.ψ hstd.2.1 Φ y z (Lm u), hi, sub_self, mul_zero,
      AddChar.map_zero_eq_one, one_mul]
  · intro u; exact hre _ ⟨u, rfl⟩
  · show 0 < (thetaSum F (schr B.ψ (Lm 0) Φ)).re
    rw [map_zero]; exact hre0
theorem lagr_invariant_unique_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ :
  E →ₐ[F] E) (B : Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : Darboux (symp (cA σ) ξ (incM F (dblG JT)ᵀ) (incM F JB)) κ),
        (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ l ∈ (adeleClass F).adm κ,
        (∀ z : Matrix (Fin nS) (Fin nT) (AF F ⊗[F] E), ∀ φ ∈ schA F κ,
          l ((GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (z * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT)
            (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ) = l φ) →
        ∃ c : ℂ, ∀ Φ ∈ schA F κ, l Φ = c * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin
          nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (thetaTr F co B.ψ
          Φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσξ₀ JB ξ hξ κ _ co hco ν 𝓕 hν h𝓕 l hl hinv
  have hstd := hB.std
  obtain ⟨L, hiso, hdim, hL⟩ := GlobalTheory.WeilSchrodinger.DiagLagr.exists_diag_lagrangian F E σ nS nT JT JB ξ κ co
    hco
  obtain ⟨l₂, hl₂, he⟩ := GlobalTheory.LagrThetaAdm.exists_admissible_eq_lagrangian_integral F E σ B hB nS nT JT
    JB ξ κ co hco ν 𝓕 hν h𝓕
  obtain ⟨φ₀, hφ₀, hne⟩ := exists_lagrInt_ne_zero_k F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕
    hν h𝓕
  have hrho : ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) (φ : (κ → AF F) → ℂ),
      (GlobalTheory.WeilSchrodinger.transD (cA σ) co).rho B.ψ (uᵀ * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin
        nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id)ᵀ) φ = co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕
        Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ := by
    intro u φ
    rw [GlobalTheory.WeilSchrodinger.transD_rho, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose]
  have hmem : ∀ w, ∀ φ ∈ schA F κ, co.rho B.ψ w φ ∈ schA F κ := fun w φ hφ =>
    GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ φ hφ
  have key : ∀ l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ,
      (∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ, l' (co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin
        nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ) = l' φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ,
        l' (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l' φ :=
          by
    intro l' h t w hw φ hφ
    obtain ⟨u, hu⟩ := hL t w hw
    rw [← hu]
    exact h u φ hφ
  obtain ⟨c, hc⟩ := GlobalTheory.AdelicSvN.main F B.ψ hstd κ L hiso hdim l hl l₂ hl₂
    (key l (fun u φ hφ => by rw [← hrho]; exact hinv _ φ hφ))
    (key l₂ (fun u φ hφ => by
      rw [he _ (hmem _ φ hφ), he φ hφ]
      exact GlobalTheory.LagrThetaInv.lagrInt_rho_inv_k F E σ B hB nS nT JT JB ξ κ co hco ν 𝓕 hν h𝓕 u φ hφ))
    ⟨φ₀, hφ₀, by rw [he φ₀ hφ₀]; exact hne⟩
  exact ⟨c, fun Φ hΦ => by rw [hc Φ hΦ, he Φ hΦ]⟩
end GlobalTheory.LagrUniq
end

section
abbrev _root_.GlobalTheory.T.lagrangian_integral_theta_model :=
  GlobalTheory.LagrThetaAdm.exists_admissible_eq_lagrangian_integral
end

noncomputable section
namespace GlobalTheory.TransportF
open Formalism.IndefR.DatumF Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.LFun GlobalTheory.WeilM IsDedekindDomain
  NumberField GlobalTheory.ThetaTransform GlobalTheory.SWQ
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E} {JA
  : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E} {ξ : AF F ⊗[F] E}
variable {κ : Type} [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ)
theorem exists_isTransportF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E
  →ₐ[F] E) (B : Base F E),
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
            ∃ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT _ _ _ _ ω hω JA JB ξ hA hB' κ _ co hrat
  have hR := hB.cm.1
  have hψ := hω.std.1
  let τ := Fintype.equivFin κ
  have he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (numCoordF co τ w) (numCoordF co τ w') := fun w w' => by
    rw [symplOF_eq_symp hA hB', co.form]
    simp only [symV, numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card κ) → F,
      numCoordF co τ (ratWF x) = (rat y, rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [numCoordF_apply]; erw [h]; rfl⟩
  have hadd : ∀ Φ ∈ schA F κ, ∀ Φ' ∈ schA F κ,
      thetaTr F co B.ψ (Φ + Φ') =
        thetaTr F co B.ψ Φ + thetaTr F co B.ψ Φ' :=
          fun Φ hΦ Φ' hΦ' => by
    simp only [thetaTr_eqF co τ]
    exact congrArg (· ∘ numCoordF co τ) (thV_add hR hψ
      (GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (comp_mem_schA τ hΦ))
      (GlobalTheory.SchwartzDecay.decay_of_mem_schA _ _ _ (comp_mem_schA τ hΦ')))
  have hinj : ∀ Φ ∈ schA F κ, ∀ Φ' ∈ schA F κ,
      thetaTr F co B.ψ Φ = thetaTr F co B.ψ Φ' → Φ = Φ' :=
    fun Φ hΦ Φ' hΦ' h => by
    simp only [thetaTr_eqF co τ] at h
    have h2 := thV_injOn hR hψ (comp_mem_schA τ hΦ) (comp_mem_schA τ hΦ')
      ((numCoordF co τ).surjective.injective_comp_right h)
    funext x
    simpa [Function.comp_def] using congrFun h2 (x ∘ τ.symm)
  have hon : ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f ↔
      ∃ Φ ∈ schA F κ, thetaTr F co B.ψ Φ = f := fun f => by
    constructor
    · intro hf
      obtain ⟨Φ, hΦ, h⟩ := GlobalTheory.T.schrodinger_model_intertwining F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ
        hω.std _ (numCoordF co τ) he hr f hf
      refine ⟨_, comp_mem_schA τ.symm hΦ, ?_⟩
      rw [thetaTr_eqF co τ, ← h]
      congr 2
      funext x
      simp [Function.comp_def]
    · rintro ⟨Φ, hΦ, rfl⟩
      rw [thetaTr_eqF co τ]
      exact GlobalTheory.T.schrodinger_model_isomorphism F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _
        (numCoordF co τ) he hr _
        (comp_mem_schA τ hΦ)
  obtain ⟨om, hom⟩ := exists_transport' _ _ _ hadd (thetaTr_smulF co) hinj hon
    (ω.comp (pairHomF hS hξ0 hA hB')) fun p f hf => hω.om_pres _ f hf
  refine ⟨om, ?_⟩
  intro a b g h hh hg Φ hΦ
  have e :=
    congrArg ω (pairHomF_eq hS hξ0 hA hB' a b g h hh hg)
  have h2 := hom (a, b) Φ hΦ
  exact ⟨h2.1, h2.2.trans (LinearMap.congr_fun e _)⟩
end GlobalTheory.TransportF
end

section
open Formalism.IndefR.DatumF Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.LFun GlobalTheory.WeilM IsDedekindDomain
  NumberField MeasureTheory
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem exists_coord_k {B : Base F E} (hB : GoodK σ B) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin
  nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0) (hσ : σ ξ₀ = -ξ₀)
      :
    (-1 : AF F ⊗[F] E) • incM F (-(ξ₀ • JS⁻¹)) = incM F (ξ₀ • JS⁻¹) ∧
    ∃ co : Darboux (symp (cA σ) (-1) (incM F JTᵀ) (incM F (-(ξ₀ • JS⁻¹)))) (Fin nT × Fin nS),
      (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin nT × Fin nS → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∃ Φ ∈ schA F (Fin nT × Fin nS), thetaTr F co B.ψ
        Φ = f := by
  have eB : (-1 : AF F ⊗[F] E) • incM F (-(ξ₀ • JS⁻¹)) = incM F (ξ₀ • JS⁻¹) := by
    funext i j
    simp [incM]
  obtain ⟨co, hrat⟩ : ∃ co : Darboux (symp (cA σ) (-1) (incM F JTᵀ) (incM F (-(ξ₀ • JS⁻¹)))) (Fin nT × Fin nS),
      ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin nT × Fin nS → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) :=
    GlobalTheory.RatDarboux.exists_darboux (AF F) hB.cm.2.2.1 σ (GlobalTheory.SplitDetCharF.sig_invol hB.cm)
    (JA := JTᵀ) (JB := -(ξ₀ • JS⁻¹)) (fun i j => hT.1 j i)
    (fun i j => by
      simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg, map_mul, hσ, inv_herm hS]; ring)
    (by rw [Matrix.det_transpose]; exact hT.2)
    (by
      rw [← neg_smul, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 hξ)) (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hS.2)).ne_zero)
  refine ⟨eB, co, hrat, fun f hf => ?_⟩
  let τ := Fintype.equivFin (Fin nT × Fin nS)
  have he : ∀ w w', symplOF σ JS JT ξ₀ w w' =
      GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF (σ :=
        σ) co τ w) (GlobalTheory.TransportF.numCoordF co τ w') := fun w w' => by
    rw [GlobalTheory.TransportF.symplOF_eq_symp rfl eB]
    refine (co.form w w').trans ?_
    simp only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply,
      comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card (Fin nT × Fin nS)) → F,
      GlobalTheory.TransportF.numCoordF co τ (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) :=
        fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩
  obtain ⟨Φ, hΦ, h⟩ := GlobalTheory.T.schrodinger_model_intertwining F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσ
    (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB) _ (GlobalTheory.TransportF.numCoordF (σ :=
      σ) co τ) he hr f hf
  refine ⟨_, GlobalTheory.TransportF.comp_mem_schA τ.symm hΦ, ?_⟩
  rw [GlobalTheory.TransportF.thetaTr_eqF co τ, ← h]
  congr 2
  funext x
  congr 1; funext i
  simp
end
theorem cont_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B :
  Base F E),
    GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT)
      E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ f, IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f →
        Continuous fun h : GAF σ (dblG JT) =>
          GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, h) f) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕 χS ωd hω f hf
  have hT' := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT
  obtain ⟨eB, co, hrat, hon⟩ := exists_coord_k hB hS hT' hξ hσ
  obtain ⟨Φ, hΦ, rfl⟩ := hon f hf
  obtain ⟨om, hom⟩ := GlobalTheory.TransportF.exists_isTransportF_k F E σ B hB _ _ JS _ hS hT' ξ₀ hξ hσ χS 1
    hω.hecS hω.hecT hω.resS
    hω.resT ωd hω _ _ _ rfl eB _ co hrat
  have hc := GlobalTheory.WeilContF.continuous_transportF_k F E σ B hB _ _ JS _ hS hT' ξ₀ hξ hσ χS 1 hω.hecS
    hω.hecT hω.resS
    hω.resT ωd hω _ _ _ rfl eB _ co hrat om hom
  obtain ⟨l, hl, hl'⟩ := GlobalTheory.T.lagrangian_integral_theta_model F E σ B hB nS nT JT _ _ _ co hrat ν 𝓕 hν
    h𝓕
  let a : GAF σ (dblG JT) →
      UG (cA σ) (incM F (dblG JT)ᵀ) := fun h => ⟨matHomF σ _ h, mem_UG h⟩
  have ha : Continuous a := Continuous.subtype_mk continuous_subtypeVal _
  refine ((hc l hl Φ hΦ).comp (ha.prodMk (continuous_const (y := 1)))).congr fun h => ?_
  obtain ⟨h1, h2⟩ := hom (a h) 1 1 h rfl (by
    rw [inv_one]
    exact Matrix.transpose_one.symm) Φ hΦ
  show l (om (a h, 1) Φ) = _
  exact (hl' _ h1).trans (congrArg (GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)) h2)
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end
