module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistributionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpaceStatement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilTbBdd
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.EvLatLatO
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.CountableMat
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.PiInfInclR
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ThetaSumRationalInvariant
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.InFrameForm
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
public import Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepRationalDarbouxFixesThetaDistribution
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.FinAlg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero

/-! # SiegelWeilHeightdictStd: Consolidated global theta-kernel definitions and proofs (SiegelWeilHeightdictStd). -/
@[expose] public section

noncomputable section

section
open scoped TensorProduct NNReal Matrix Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw
open Matrix (det_mul fromBlocks transpose_mul)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace PositivityTheory.SiegelWeilFormula
section
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
  PositivityTheory.SiegelWeilFormula.KWhit.Ht
namespace HeightDict
theorem fin_std_k (d : SD_k σ) (n : ℕ) (t u : GL (Fin n) (AE F E)) (η : E) (hη : η ≠ 0) :
    (∀ v : HeightOneSpectrum (𝓞 F),
      Gen.IsCO (latM v ((t.1.map (GlobalTheory.AdelicU.compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR
          (v.adicCompletion F) σ))) ∧
      Gen.IsCO (latM v (((inclR (F := F) (v.adicCompletion F) η) • u.1.map (GlobalTheory.AdelicU.compFin F E v)).map
        (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)))) ∧
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ((latM v ((t.1.map (GlobalTheory.AdelicU.compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR
          (v.adicCompletion F) σ)) :
        Set (Fin n → v.adicCompletion F ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v) ∧
      ((latM v (((inclR (F := F) (v.adicCompletion F) η) • u.1.map (GlobalTheory.AdelicU.compFin F E v)).map
        (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)) : Set (Fin n → v.adicCompletion F ⊗[F] E)) =
          PositivityTheory.PfSWUS.Loc.latO d.bs v) := by
  classical
  have hinv1 : ∀ v : HeightOneSpectrum (𝓞 F),
      (t.1.map (compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) *
        ((t⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR
            (v.adicCompletion F) σ) = 1 := by
    intro v
    have h := congrArg (fun M => (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ).mapMatrix
      ((compFin F E v).mapMatrix M)) (Units.mul_inv t)
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
  have hinv2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ((inclR (F := F) (v.adicCompletion F) η) • u.1.map (compFin F E v)).map
          (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) *
        ((inclR (F := F) (v.adicCompletion F) η⁻¹) • (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)).map
          (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
    intro v
    have hu : u.1.map (compFin F E v) * (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v) = 1 := by
      have h := congrArg (fun M => (compFin F E v).mapMatrix M) (Units.mul_inv u)
      simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
    have hc : inclR (F := F) (v.adicCompletion F) η * inclR (F := F) (v.adicCompletion F) η⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hη, map_one]
    have h2 : (inclR (F := F) (v.adicCompletion F) η • u.1.map (compFin F E v)) *
        (inclR (F := F) (v.adicCompletion F) η⁻¹ • (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hu, smul_smul, hc, one_smul]
    have h := congrArg (fun M => (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ).mapMatrix M) h2
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
  refine ⟨fun v => ⟨latM_isCO v _ (Matrix.isUnit_det_of_right_inverse (hinv1 v)),
    latM_isCO v _ (Matrix.isUnit_det_of_right_inverse (hinv2 v))⟩, ?_⟩
  have ent : ∀ M : Matrix (Fin n) (Fin n) (AE F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ i j, compFin F E v (M i j) ∈ OE E v := fun M =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_OE (M i j)
  filter_upwards [ent t.1, ent (t⁻¹ : GL (Fin n) (AE F E)).1, ent u.1, ent (u⁻¹ : GL (Fin n) (AE F E)).1,
    ev_inclR (F := F) η, ev_inclR (F := F) η⁻¹, ev_lat_latO d.bs n] with v ht ht' hu hu' he he' hl
  refine ⟨?_, ?_⟩
  · rw [latM_eq_lat v _ _ (hinv1 v) (fun i j => OE_sig v (ht i j)) (fun i j => OE_sig v (ht' i j)), hl]
  · rw [latM_eq_lat v _ _ (hinv2 v) (fun i j => OE_sig v (OE_mul v he (hu i j)))
      (fun i j => OE_sig v (OE_mul v he' (hu' i j))), hl]
end HeightDict
end
namespace Tauto
theorem thetaSum_S_rat_k (hP : TPar_k) (hT : TTheta_k) (d : SD_k σ) {γ : UA σ d.A.J} (hγ : γ ∈ ratU σ d.A.J)
    {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) : thetaSum F (d.S γ Ψ) = thetaSum F Ψ := by
  have hS := d.ok.dbl.lin.pres γ Ψ hΨ
  obtain ⟨g₀, hg₀⟩ := PositivityTheory.ThKF0.Resc.rat_mat (inv_mem hγ)
  obtain ⟨g₁, hg₁⟩ := PositivityTheory.ThKF0.Resc.rat_mat hγ
  have hinj : Function.Injective (incM F : Matrix (Fin d.m) (Fin d.m) E → Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    kfour.incM_injective
  have hmul : ∀ {p q r : ℕ} (A : Matrix (Fin p) (Fin q) E) (B : Matrix (Fin q) (Fin r) E),
      incM F (A * B) = incM F A * incM F B := fun A B => Matrix.map_mul (f := inclR (F := F) (E := E) (AF F))
  have hone : incM F (1 : Matrix (Fin d.m) (Fin d.m) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have e01 : g₀ * g₁ = 1 := hinj (by
    rw [hmul, ← hg₀, ← hg₁, hone]
    simp)
  have e10 : g₁ * g₀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 e01
  let e : d.ME ≃ d.ME :=
    ⟨fun X => g₀ * X, fun X => g₁ * X, fun X => by simp [← Matrix.mul_assoc, e10], fun X => by simp [← Matrix.mul_assoc,
        e01]⟩
  have h1 := (hT F E σ d (d.S γ Ψ) hS).1
  have h2 := (hT F E σ d Ψ hΨ).1
  have h3 : HasSum (fun X : d.ME => d.T Ψ (incM F (e X))) (thetaSum F (d.S γ Ψ)) := by
    refine h1.congr_fun fun X => ?_
    rw [(hP F E σ d Ψ hΨ).2.2 γ (incM F X)]
    simp only [e, Equiv.coe_fn_mk, hmul, mat, ← hg₀]
  exact h3.unique ((e.hasSum_iff).2 h2)
section
open PositivityTheory.ThKF0.Resc in

theorem thetaSum_rational_invariant (d : SD_k σ) (γ : d.G) (hγ : γ ∈ d.r2) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) :
    thetaSum F (d.om γ Ψ) = thetaSum F Ψ := by
  have hσ : IsCMExt F E σ := d.cm
  have hψ : IsStd d.B.ψ := d.std
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  let : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨δ, hq⟩ := exists_isQuad hσ
  have h0 : δ ≠ 0 := hq.unit.ne_zero
  obtain ⟨-, hS, hR⟩ := d.ok.dbl.weil
  have hYd : d.Y.J.det ≠ 0 := by
    obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
    intro hz
    have hee : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    have hM : (fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 : Matrix d.N2 d.N2 E) *
        fromBlocks 0 (((ε : ℤ) : E) • 1) 1 0 = 1 := by
      rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [smul_smul, hee]
    have h1 := congrArg Matrix.det hM
    rw [det_mul, ← hε, det_mul, det_mul, dbl, Matrix.det_fromBlocks_zero₂₁, hz] at h1
    simp at h1
  have hκ : Fintype.card d.κ = Fintype.card (Fin d.m) * Fintype.card d.N2 := by
    have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    let bE : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
    let bA := Algebra.TensorProduct.basis (AF F) bE
    have : Module.Free (AF F) (AE F E) := Module.Free.of_basis bA
    have : Module.Finite (AF F) (AE F E) := Module.Finite.of_basis bA
    have e := d.dd.e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_eq_card_basis bA, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card] at e
    simp only [Fintype.card_fin, Fintype.card_sum] at e ⊢
    omega
  obtain ⟨d₀, hd₀⟩ := exists_ratCoord h2 hκ d.dd.e d.ok.dbl.rat
  obtain ⟨a, b, hab, hA, hB⟩ : ∃ a b : E, -1 = δ * a * b ∧ IsHerm σ (a • d.A.J) ∧ IsHerm σ (b • d.Y.J) := by
    rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
    · refine ⟨1, -δ⁻¹, by field_simp, ?_, ?_⟩
      · rw [one_smul]; exact ⟨hA.herm, (herm_det hA).isUnit⟩
      · refine ⟨fun i j => by simp [hY i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hYd
    · refine ⟨-δ⁻¹, 1, by field_simp, ?_, ?_⟩
      · refine ⟨fun i j => by simp [hA.skew i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) (skew_det hA)
      · rw [one_smul]; exact ⟨hY, hYd.isUnit⟩
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hξ : (-1 : AE F E) = inclR (F := F) (AF F) δ * inclR (F := F) (AF F) a * inclR (F := F) (AF F) b := by
    rw [← map_mul, ← map_mul, ← hab, map_neg, map_one]
  have hJA : incM F (a • d.A.J) = inclR (F := F) (AF F) a • incM F d.A.J := by
    ext i j; simp [incM]
  have hJB : incM F (dbl (b • d.Y.J)) = inclR (F := F) (AF F) b • dbl (incM F d.Y.J) := by
    ext (i | i) (j | j) <;> simp [incM, dbl]
  obtain ⟨d', om', he, hS', hR', hgg⟩ := split_resc (c := cA σ) (C := adeleClass F) (ψ := d.B.ψ) (κ := d.κ) hξ
    (hb.isUnit.map (inclR (F := F) (AF F))) hJA hJB hS.toIsSplitting hR
  have hd' : ∀ x, d'.e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F)
      ((d₀ x).2 i)) :=
    fun x => by rw [he]; exact hd₀ x
  obtain ⟨g', hg'1, hg'2⟩ := hgg γ
  have hg : ∃ γ₀ : Matrix d.N2 d.N2 E,
      ((g' : GL d.N2 (AE F E)) : d.Mn2) = incM F γ₀ :=
          by
    obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
    refine ⟨g₀, ?_⟩
    rw [hg'1, ← hg₀]
    rfl
  rw [← hg'2]
  exact split_core hψ hq (a • d.A.J) (b • d.Y.J) hA hB d' d₀ hd' d.χ d.ok.hecke om' hS' hR' g' hg Ψ hΨ
end
theorem cpt_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD_k σ) : Cpt σ d.A.J := by
  have h := cptAll_of_k PositivityTheory.ThKEst.grpTop_of _root_.PositivityTheory.ThKEst.epsOf_of_k
      (PositivityTheory.ThKEst.siegelAll_of hS)
    PositivityTheory.ThKEst.finVolU PositivityTheory.ThKF.unimodularity_holds
  rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
  · exact h F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inl hA) d.ok.aniso
  · exact h F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inr hA) d.ok.aniso
theorem exists_lth_k (d : SD_k σ) : ∃ l ∈ (adeleClass F).adm d.κ, ∀ Φ ∈ d.sch, l Φ = thetaSum F Φ :=
  GlobalTheory.T.exists_admitted_form_eq_adelicThetaDistribution F d.κ
theorem cont_S_k (d : SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) : Continuous fun g : UA σ d.A.J => thetaSum F (d.S g Ψ) := by
  obtain ⟨l, hl, hlθ⟩ := exists_lth_k d
  exact (d.ok.dbl.lin.cont l hl Ψ hΨ).congr fun g => hlθ _ (d.ok.dbl.lin.pres g Ψ hΨ)
theorem inv_S_k (hP : TPar_k) (hT : TTheta_k) (d : SD_k σ) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) :
    ∀ γ ∈ ratU σ d.A.J, ∀ g, thetaSum F (d.S (γ * g) Ψ) = thetaSum F (d.S g Ψ) := fun γ hγ g => by
  rw [map_mul, mul_apply_eq_comp, thetaSum_S_rat_k hP hT d hγ (d.ok.dbl.lin.pres g Ψ hΨ)]
theorem bdd_S_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : TPar_k) (hT : TTheta_k) (d : SD_k σ) {Ψ : d.Fn}
    (hΨ : Ψ ∈ d.sch) :
    ∃ C : ℝ, ∀ g, ‖thetaSum F (d.S g Ψ)‖ ≤ C :=
  (cpt_k hS d).bdd (cont_S_k d hΨ) (inv_S_k hP hT d hΨ)
theorem intOn_S_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : TPar_k) (hT : TTheta_k) (d : SD_k σ) {Ψ : d.Fn}
    (hΨ : Ψ ∈ d.sch) :
    IntegrableOn (fun g => thetaSum F (d.S g Ψ)) d.D d.μ := by
  obtain ⟨C, hC⟩ := bdd_S_k hS hP hT d hΨ
  exact Measure.integrableOn_of_bounded (M := C) ((cpt_k hS d).fin d.μ d.D d.ok.haar d.ok.dom).ne
    (cont_S_k d hΨ).aestronglyMeasurable (Eventually.of_forall hC)
theorem exists_meanAdm_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : TPar_k) (hT : TTheta_k) (d : SD_k σ) :
    ∃ Λ ∈ (adeleClass F).adm d.κ, ∀ Ψ ∈ d.sch,
      Λ Ψ = (d.μ.real d.D)⁻¹ • ∫ g in d.D, thetaSum F (d.S g Ψ) ∂d.μ := by
  obtain ⟨l, hl, hlθ⟩ := exists_lth_k d
  have hpres : ∀ g, ∀ Ψ ∈ d.sch, d.S g Ψ ∈ d.sch := fun g Ψ hΨ => d.ok.dbl.lin.pres g Ψ hΨ
  have hfun : ∀ Ψ ∈ d.sch, (fun g => l (d.S g Ψ)) = fun g => thetaSum F (d.S g Ψ) :=
    fun Ψ hΨ => funext fun g => hlθ _ (hpres g Ψ hΨ)
  have hint : ∀ Ψ ∈ d.sch, IntegrableOn (fun g => l (d.S g Ψ)) d.D d.μ := fun Ψ hΨ => by
    rw [hfun Ψ hΨ]; exact intOn_S_k hS hP hT d hΨ
  set c : ℝ := (d.μ.real d.D)⁻¹ with hc
  let L0 : d.sch →ₗ[ℂ] ℂ :=
    { toFun := fun Ψ => c • ∫ g in d.D, l (d.S g Ψ.1) ∂d.μ
      map_add' := fun Ψ Ψ' => by
        simp only [Submodule.coe_add, map_add (f := _)]
        rw [integral_add (hint _ Ψ.2) (hint _ Ψ'.2), smul_add]
      map_smul' := fun a Ψ => by
        simp only [SetLike.val_smul, map_smul, RingHom.id_apply, smul_eq_mul]
        rw [integral_const_mul, mul_smul_comm] }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend L0
  have hΛv : ∀ Ψ (hΨ : Ψ ∈ d.sch), Λ Ψ = c • ∫ g in d.D, l (d.S g Ψ) ∂d.μ := fun Ψ hΨ => by
    have := congrArg (fun L => L ⟨Ψ, hΨ⟩) hΛ
    simpa [L0] using this
  refine ⟨Λ, fun gf hgf => ?_, fun Ψ hΨ => by rw [hΛv Ψ hΨ, hfun Ψ hΨ]⟩
  choose Th hTh using fun h : UA σ d.A.J => d.ok.dbl.lin.adm h l hl gf hgf
  have hmem : ∀ f : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f gf ∈ d.sch :=
    fun f => Submodule.subset_span ⟨f, gf, hgf, rfl⟩
  have hTv : ∀ h f, Th h f = thetaSum F (d.S h (pureA F f gf)) := fun h f => by
    rw [← hTh h f, LinearMap.comp_apply, hlθ _ (hpres h _ (hmem f))]
  have : BarrelledSpace ℂ (SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ) :=
      GlobalTheory.T.schwartzMap_barrelledSpace' _
  have hUE : UniformEquicontinuous ((↑) ∘ Th) := (norm_withSeminorms ℂ ℂ).banach_steinhaus fun _ f => by
    obtain ⟨C, hC⟩ := bdd_S_k hS hP hT d (hmem f)
    refine ⟨C, ?_⟩
    rintro _ ⟨h, rfl⟩
    simpa [hTv] using hC h
  have hpa : ∀ f f' : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ,
      pureA F (f + f') gf = pureA F f gf + pureA F f' gf := fun f f' => funext fun x => by
    simp [pureA, add_mul]
  have hps : ∀ (a : ℂ) (f : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ),
      pureA F (a • f) gf = a • pureA F f gf := fun a f => funext fun x => by
    simp [pureA, mul_assoc]
  let Lf : SchwartzMap (d.κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun f => Λ (pureA F f gf)
      map_add' := fun f f' => by rw [hpa, map_add (f := _)]
      map_smul' := fun a f => by rw [hps, map_smul]; rfl }
  have hLf : ∀ f, Lf f = c • ∫ g in d.D, Th g f ∂d.μ := fun f => by
    show Λ (pureA F f gf) = _
    rw [hΛv _ (hmem f)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show l (d.S g (pureA F f gf)) = Th g f
    rw [← hTh g f]; rfl
  have hfin := (cpt_k hS d).fin d.μ d.D d.ok.haar d.ok.dom
  have hpos : 0 < d.μ.real d.D := by
    have := (cpt_k hS d).cnt
    have := d.ok.haar
    exact ENNReal.toReal_pos (fd_ne d.ok.dom) hfin.ne
  have hcont : Continuous Lf := by
    refine continuous_of_continuousAt_zero Lf.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(Metric.equicontinuousAt_iff_right.1 (hUE.equicontinuous 0)) (ε / 2) (half_pos hε)] with f hf
    rw [dist_zero_right]
    show ‖Lf f‖ < ε
    rw [hLf]
    have hb : ∀ g ∈ d.D, ‖Th g f‖ ≤ ε / 2 := fun g _ => by
      have := (hf g).le
      simpa [dist_comm] using this
    calc ‖c • ∫ g in d.D, Th g f ∂d.μ‖ ≤ c * (ε / 2 * d.μ.real d.D) := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
          gcongr
          exact norm_setIntegral_le_of_norm_le_const hfin hb
      _ = ε / 2 := by rw [hc]; field_simp
      _ < ε := half_lt_self hε
  exact ⟨⟨Lf, hcont⟩, fun f => rfl⟩
end Tauto
namespace Tauto
open kfour Place
section
variable (d : SD_k σ)
theorem frame_sign_k : ∃ ε : ℤˣ, FrameEq σ d.Y d.b ε ∧
    ∀ i j, d.A.J j i = -(((ε : ℤ) : E)) * σ (d.A.J i j) := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  refine ⟨ε, hε, ?_⟩
  have key : ∀ e : E, e * e = 1 → (∀ i j, σ (d.Y.J j i) = e * d.Y.J i j) → ((ε : ℤ) : E) = e := by
    intro e he hY
    have hY' : ∀ i j, d.Y.J j i = e * σ (d.Y.J i j) := fun i j => by
      rw [hY j i, ← mul_assoc, he, one_mul]
    have hD : (dbl d.Y.J)ᵀ = e • (dbl d.Y.J).map σ := by
      ext (i | i) (j | j)
      · simp [dbl, hY' i j]
      · simp [dbl]
      · simp [dbl]
      · simp [dbl, hY' i j]
    have hM : (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ)ᵀ = e • (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ).map σ := by
      have e1 : (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ).map σ = (d.b.1.map σ)ᵀ * (dbl d.Y.J).map σ * d.b.1 := by
        have h1 : ∀ {p q r : Type} [Fintype q] (P : Matrix p q E) (Q : Matrix q r E), (P * Q).map σ = P.map σ *
            Q.map σ :=
          fun P Q => Matrix.map_mul (f := σ.toRingHom)
        have h2 : (d.b.1.map σ).map σ = d.b.1 := by
          rw [Matrix.map_map]
          exact Matrix.ext fun i j => hσ _
        rw [h1, h1, h2, Matrix.transpose_map]
      rw [e1, transpose_mul, transpose_mul, Matrix.transpose_transpose, hD, Matrix.smul_mul,
          Matrix.mul_smul,
        Matrix.mul_assoc]
    rw [hε] at hM
    have hn := d.ok.hn
    have := congrFun (congrFun hM (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
    simpa [fromBlocks] using this
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · have e := key (-1) (by ring) fun i j => by rw [hY i j]; ring
    intro i j
    rw [e, neg_neg, one_mul]
    exact (hA.herm j i).symm
  · have e := key 1 (by ring) fun i j => by rw [hY i j, one_mul]
    intro i j
    rw [e, hA.skew j i]
    ring
theorem gram_cond_k (ε : ℤˣ) (hε : ∀ i j, d.A.J j i = -(((ε : ℤ) : E)) * σ (d.A.J i j))
    (X : d.MxE) : d.gram X X ∈ nCond σ d.n ε := by
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  have hJ : (incM F d.A.J)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F d.A.J).map (cA σ)) := by
    ext i j
    simp only [Matrix.transpose_apply, incM, Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul,
      cA_inclR']
    rw [hε i j, map_mul, map_neg, inclR_int, neg_mul]
  show (Xᵀ * incM F d.A.J * X.map (cA σ))ᵀ = -((((ε : ℤ) : AE F E)) • (Xᵀ * incM F d.A.J * X.map (cA σ)).map (cA σ))
  have h1 : ∀ {p q r : Type} [Fintype q] (P : Matrix p q (AE F E)) (Q : Matrix q r (AE F E)),
      (P * Q).map (cA σ) = P.map (cA σ) * Q.map (cA σ) := fun P Q => Matrix.map_mul (f := (cA σ).toRingHom)
  have h2 : (X.map (cA σ)).map (cA σ) = X := by
    rw [Matrix.map_map]
    exact Matrix.ext fun i j => cA_cA' σ hσ _
  rw [h1, h1, h2, Matrix.transpose_map, transpose_mul, transpose_mul, Matrix.transpose_transpose, hJ,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
theorem gram_incM_k (X : d.ME) :
    d.gram (incM F X) (incM F X) = incM F (Xᵀ * d.A.J * X.map σ) := by
  show (incM F X)ᵀ * incM F d.A.J * (incM F X).map (cA σ) = _
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul', _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul', incM_map]
  rfl
theorem gram_mem_k (X : d.ME) (T : d.nF_) :
    ⅟(2 : AF F) • d.gram (incM F X) (incM F X) + T.1.1 ∈ d.nA_ ∧
      ∃ S₀ : Matrix (Fin d.n) (Fin d.n) E, ⅟(2 : AF F) • d.gram (incM F X) (incM F X) + T.1.1 = incM F S₀ := by
  obtain ⟨ε, hb, hε⟩ := frame_sign_k d
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨T₀, hT₀⟩ := (mem_nF_iff T.1).1 T.2
  refine ⟨(mem_nA_iff hσ hb _).2 (add_mem (smul_cond ε _ (gram_cond_k d ε hε _)) ((mem_nA_iff hσ hb _).1 T.1.2)),
    (2⁻¹ : E) • (Xᵀ * d.A.J * X.map σ) + T₀, ?_⟩
  rw [gram_incM_k, hT₀]
  ext i j
  simp only [incM, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_add (f := _), map_mul]
  rw [Algebra.smul_def, ← half_eq]
theorem exists_twist_k (ε : ℤˣ) (S₀ : Matrix (Fin d.n) (Fin d.n) E) (hS : incM F S₀ ∈ nCond σ d.n ε)
    (h0 : S₀ ≠ 0) : ∃ β₀ ∈ nCond σ d.n ε, d.B.ψ (-(d.tt (incM F S₀ * β₀))) ≠ 1 := by
  have hcm := d.cm
  have hS' : (incM F S₀)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F S₀).map (cA σ)) := hS
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, S₀ i j ≠ 0 := by
    by_contra h
    exact h0 (Matrix.ext fun i j => by_contra fun hne => h ⟨i, j, hne⟩)
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ := d.B.emb
  set Sw : d.Mnc := (incM F S₀).map (piInf (τ w)) with hSw
  have hSwT : ∀ i j, Sw j i = -(((ε : ℤ) : ℂ)) * star (Sw i j) := fun i j => by
    have := congrArg (fun M => (M.map (piInf (τ w))) i j) hS'
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg,
      map_mul, map_intCast, piInf_cA hcm] at this
    simpa [hSw] using this
  set q : ℂ := piInf (τ w) ((incM F S₀ * incM F S₀).trace) with hq
  have hqe : q = -(((ε : ℤ) : ℂ)) * ∑ i, ∑ j, ((Complex.normSq (Sw i j) : ℝ) : ℂ) := by

    rw [hq, Matrix.trace, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [Matrix.diag_apply, Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    change Sw i j * Sw j i = _
    rw [hSwT i j, Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring
  have hN : 0 < ∑ i, ∑ j, Complex.normSq (Sw i j) := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (Sw i j))
      (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i₀))
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => Complex.normSq (Sw i₀ j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ j₀))
    refine Complex.normSq_pos.2 ?_
    simp only [hSw, Matrix.map_apply, incM, piInf_inclR']
    exact (map_ne_zero _).2 hij
  have hε1 : (((ε : ℤ) : ℝ)) ≠ 0 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hqre : q.re = -(((ε : ℤ) : ℝ)) * ∑ i, ∑ j, Complex.normSq (Sw i j) := by
    rw [hqe]
    simp [Complex.mul_re, ← Complex.ofReal_sum]
  have hqre0 : q.re ≠ 0 := by
    rw [hqre]
    exact mul_ne_zero (neg_ne_zero.2 hε1) hN.ne'
  set r : ℝ := -1 / (4 * q.re) with hr
  obtain ⟨s, -, hs1, hs2, -, hs4⟩ := exists_sec hcm τ
  set x : InfinitePlace F → ℂ := fun u => if u = w then (r : ℂ) else 0 with hx
  set c := s x with hc
  have hcc : cA σ c = c := by
    refine ad_ext hcm τ (fun u => ?_) ?_
    · rw [piInf_cA hcm, hc, hs1]
      by_cases hu : u = w <;> simp [hx, hu]
    · rw [← map_smul, hc, hs2, map_zero]
  refine ⟨c • incM F S₀, ?_, ?_⟩
  · show (c • incM F S₀)ᵀ = -((((ε : ℤ) : AE F E)) • (c • incM F S₀).map (cA σ))
    have e : (c • incM F S₀).map (cA σ) = c • (incM F S₀).map (cA σ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hcc]
    rw [Matrix.transpose_smul, hS', e, smul_neg, smul_comm]
  · set z := -(c * (incM F S₀ * incM F S₀).trace) with hz
    have e1 : -(d.tt (incM F S₀ * (c • incM F S₀))) = Algebra.trace (AF F) (AE F E) z := by
      rw [hz, map_neg, SD_k.tt, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hf : finOne F • z = 0 := by
      rw [hz, smul_neg, ← smul_mul_assoc, hc, hs2, zero_mul, neg_zero]
    have hw : ∀ u, u ≠ w → piInf (τ u) z = 0 := fun u hu => by
      rw [hz, map_neg, map_mul, hc, hs1]
      simp [hx, hu]
    rw [e1, psi_trace_at d.std hcm τ w z hf hw]
    have hzw : (piInf (τ w) z).re = 1 / 4 := by
      rw [hz, map_neg, map_mul, hc, hs1, ← hq]
      simp only [hx, ite_eq_left rfl, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero]
      rw [hr]
      field_simp
    rw [hzw]
    intro h
    have h2 : Complex.exp (-(2 * Real.pi * Complex.I) * (((2 * (1 / 4 : ℝ)) : ℝ) : ℂ)) = -1 := by
      rw [show (2 * (1 / 4 : ℝ)) = 1 / 2 by norm_num]
      rw [show -(2 * Real.pi * Complex.I) * (((1 / 2 : ℝ)) : ℂ) = -(Real.pi * Complex.I) by push_cast; ring]
      rw [Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    rw [h2] at h
    norm_num at h
theorem orth_k {nb : d.nA_ → d.G} {lam : Measure d.nA_} {𝓖 : Set d.nA_}
    (hc : d.CD nb lam 𝓖) (S : d.Mn)
    (hS : S ∈ d.nA_) (hr : ∃ S₀ : Matrix (Fin d.n) (Fin d.n) E, S = incM F S₀) :
    ∫ β in 𝓖, d.B.ψ (-(d.tt (S * β.1))) ∂lam = if S = 0 then 1 else 0 := by
  classical
  obtain ⟨ε, hb, -⟩ := frame_sign_k d
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  have : lam.IsAddHaarMeasure := hc.2.1
  have hfd : IsAddFundamentalDomain d.nF_ 𝓖 lam := hc.2.2.1
  have h1 : lam 𝓖 = 1 := hc.2.2.2
  have : BorelSpace d.nA_ := (nA_top hσ d.ok.frame).2.2.2
  obtain ⟨S₀, rfl⟩ := hr
  split_ifs with h0
  · have hone : ∀ β : d.nA_, d.B.ψ (-(d.tt (incM F S₀ * β.1))) = 1 := fun β => by
      rw [h0, Matrix.zero_mul, SD_k.tt, Matrix.trace_zero, map_zero, neg_zero, AddChar.map_zero_eq_one]
    simp_rw [hone]
    rw [setIntegral_const]
    erw [Measure.real_def, h1]; simp
  · have hS0 : S₀ ≠ 0 := fun h => h0 (by rw [h]; ext i j; simp [incM])
    obtain ⟨β₀, hβ₀, hne⟩ := exists_twist_k d ε S₀ ((mem_nA_iff hσ hb _).1 hS) hS0
    let h : d.nA_ → ℂ := fun β => d.B.ψ (-(d.tt (incM F S₀ * β.1)))
    have hadd : ∀ β β' : d.nA_, h (β + β') = h β * h β' := fun β β' => by
      simp only [h, AddSubgroup.coe_add, Matrix.mul_add, SD_k.tt, Matrix.trace_add, map_add (f := _), neg_add,
        AddChar.map_add_eq_mul]
    have hper : ∀ g ∈ d.nF_, ∀ y, h (g + y) = h y := fun g hg y => by
      obtain ⟨T₀, hT₀⟩ := (mem_nF_iff g).1 hg
      rw [hadd]
      have hg1 : h g = 1 := by
        simp only [h, hT₀, ← _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul', SD_k.tt, trace_incM, trace_inclR, ← map_neg]
        exact d.std.2.1 _
      rw [hg1, one_mul]
    exact GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist lam d.nF_ hfd hper
      (c := ⟨β₀, (mem_nA_iff hσ hb _).2 hβ₀⟩) (fun y => hadd _ y) hne
end
theorem thetaAuto_at_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : TPar_k) (hT : TTheta_k) (d : SD_k σ) :
    d.μ d.D ≠ 0 ∧ d.μ d.D ≠ ⊤ ∧ ∀ Φ ∈ d.sch,
      (∀ x, IntegrableOn (fun g => thetaSum F (d.om x (d.S g Φ))) d.D d.μ) ∧ Continuous (d.I Φ) ∧
      ∀ γ ∈ d.r2, ∀ x, d.I Φ (γ * x) = d.I Φ x := by
  have hc := cpt_k hS d
  have := hc.cnt
  have := d.ok.haar
  have hom : ∀ x, ∀ Ψ ∈ d.sch, d.om x Ψ ∈ d.sch := fun x Ψ hΨ => d.ok.dbl.weil.2.1.pres x Ψ hΨ
  have hcomm : ∀ Φ ∈ d.sch, ∀ x g, d.om x (d.S g Φ) = d.S g (d.om x Φ) := fun Φ hΦ => (hT F E σ d Φ hΦ).2
  obtain ⟨Λ, hΛ, hΛv⟩ := exists_meanAdm_k hS hP hT d
  refine ⟨fd_ne d.ok.dom, (hc.fin d.μ d.D d.ok.haar d.ok.dom).ne, fun Φ hΦ => ⟨fun x => ?_, ?_, fun γ hγ x => ?_⟩⟩
  · simp only [hcomm Φ hΦ]
    exact intOn_S_k hS hP hT d (hom x Φ hΦ)
  · have e : d.I Φ = fun x => Λ (d.om x Φ) := funext fun x => by
      rw [hΛv _ (hom x Φ hΦ)]
      show thetaMean d.om d.S d.μ d.D Φ x = _
      rw [thetaMean, setAverage_eq]
      simp only [hcomm Φ hΦ]
    rw [e]
    exact d.ok.dbl.weil.2.1.cont Λ hΛ Φ hΦ
  · show thetaMean d.om d.S d.μ d.D Φ (γ * x) =
        thetaMean d.om d.S d.μ d.D Φ x
    simp only [thetaMean, map_mul, mul_apply_eq_comp]
    refine congrArg (fun f : UA σ d.A.J → ℂ => ⨍ g in d.D, f g ∂d.μ) (funext fun g => ?_)
    exact thetaSum_rational_invariant d γ hγ _ (hom x _ (d.ok.dbl.lin.pres g Φ hΦ))
theorem thetaAuto_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hP : TPar_k) (hT : TTheta_k) : ThetaAuto_k :=
  fun _ _ _ _ _ _ _ _ d => thetaAuto_at_k hS hP hT d
section
variable (d : SD_k σ)
def tr_k (g : UA σ d.A.J) (X : d.ME) : d.MxE := mat g⁻¹ * incM F X
theorem cont_tr_k {f : d.MxE → ℂ} (hf : f ∈ d.schM) (X : d.ME) :
    Continuous fun g : UA σ d.A.J => f (tr_k d g X) := by
  have h1 := PositivityTheory.ThKEst.continuous_schA (Φ := f ∘ d.cmb) hf
  have e : ∀ Y, f Y = (f ∘ d.cmb) (d.crd Y) := fun Y => by simp [Kdil.Tb.cmb_crd_k]
  have h2 : Continuous fun h : UA σ d.A.J =>
      (((h : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    Units.continuous_coe_inv.comp continuous_subtypeVal
  simp only [tr_k, e, Kdil.Tb.crd_mul_k]
  exact h1.comp (((Kdil.Tb.continuous_mh_k d).comp h2).matrix_mulVec continuous_const)
theorem chr_comb_k (β G T : d.Mn) :
    d.B.ψ (-(⅟(2 : AF F) * d.tt (β * G))) * d.B.ψ (-(d.tt (T * β))) =
      d.B.ψ (-(d.tt ((⅟(2 : AF F) • G + T) * β))) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [SD_k.tt, add_mul, Matrix.trace_add, smul_mul_assoc, Matrix.trace_smul, map_add (f := _), map_smul,
      smul_eq_mul,
    Matrix.trace_mul_comm G β]
  ring
theorem half_eq_iff_k (G T : d.Mn) :
    ⅟(2 : AF F) • G + T = 0 ↔ G = (-2 : ℤ) • T := by
  have h2 : algebraMap (AF F) (AE F E) ⅟(2 : AF F) * 2 = 1 := by
    rw [← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self, map_one]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def] at this
    rw [Matrix.smul_apply, zsmul_eq_mul]
    push_cast
    linear_combination 2 * this - G i j * h2
  · rintro rfl
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, Matrix.smul_apply, zsmul_eq_mul]
    push_cast
    linear_combination (-T i j) * h2
end
theorem stepA_k (hP : TPar_k) (hT : TTheta_k) (d : SD_k σ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {nb : d.nA_ → d.G}
    (hnb : IsNMap (Y := d.Y) d.b nb) (x : d.G) (β : d.nA_) (g : UA σ d.A.J) :
    thetaSum F (d.om (nb β * x) (d.S g Φ)) = ∑' X : d.ME,
      d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * d.gram (incM F X) (incM F X)))) * d.T (d.om x Φ) (tr_k d g X) := by
  have hΨ := d.ok.dbl.weil.2.1.pres x Φ hΦ
  have hΨg : d.S g (d.om x Φ) ∈ d.sch := d.ok.dbl.lin.pres g _ hΨ
  have hn : d.om (nb β) (d.S g (d.om x Φ)) ∈ d.sch := d.ok.dbl.weil.2.1.pres (nb β) _ hΨg
  rw [map_mul, mul_apply_eq_comp, (hT F E σ d Φ hΦ).2 x g, ← ((hT F E σ d _ hn).1).tsum_eq]
  refine tsum_congr fun X => ?_
  rw [(hP F E σ d _ hΨg).1 (nb β) β.1 (hnb β) (incM F X), (hP F E σ d _ hΨ).2.2 g (incM F X)]
  rfl
theorem meas_tr_k (d : SD_k σ) {f : d.MxE → ℂ} (hf : f ∈ d.schM) (X : d.ME) :
    AEMeasurable (fun g => ‖f (tr_k d g X)‖ₑ) (d.μ.restrict d.D) :=
  ((cont_tr_k d hf X).eNorm.measurable).aemeasurable
theorem tbdd_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD_k σ) {f : d.MxE → ℂ} (hf : f ∈ d.schM) :
    ∃ K : ℝ, ∀ g : UA σ d.A.J, Summable (fun X => ‖f (tr_k d g X)‖) ∧ ∑' X, ‖f (tr_k d g X)‖ ≤ K := by
  obtain ⟨K, hK⟩ := Kdil.thetaBdd_of_k hS F E σ d f hf
  exact ⟨K, hK⟩
theorem pt_bdd_k (d : SD_k σ) {f : d.MxE → ℂ} (g : UA σ d.A.J) (s : Set (d.ME)) {K : ℝ}
    (hsum : Summable (fun X => ‖f (tr_k d g X)‖)) (hle : ∑' X, ‖f (tr_k d g X)‖ ≤ K) :
    ∑' X : s, ‖f (tr_k d g X.1)‖ₑ ≤ ENNReal.ofReal K := by
  calc ∑' X : s, ‖f (tr_k d g X.1)‖ₑ ≤ ∑' X, ‖f (tr_k d g X)‖ₑ :=
        tsum_comp_le_tsum_of_injective Subtype.val_injective (fun X => ‖f (tr_k d g X)‖ₑ)
    _ = ∑' X, ENNReal.ofReal ‖f (tr_k d g X)‖ := tsum_congr fun X => (ofReal_norm _).symm
    _ = ENNReal.ofReal (∑' X, ‖f (tr_k d g X)‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsum).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hle
theorem lint_fin_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD_k σ) {f : d.MxE → ℂ}
    (hf : f ∈ d.schM)
    (s : Set (d.ME)) :
    ∑' X : s, ∫⁻ g in d.D, ‖f (tr_k d g X.1)‖ₑ ∂d.μ ≠ ⊤ := by
  have := countable_mat (E := E) d.m d.n
  obtain ⟨K, hK⟩ := tbdd_k hS d hf
  have hfin := (cpt_k hS d).fin d.μ d.D d.ok.haar d.ok.dom
  rw [← lintegral_tsum (f := fun (X : s) g => ‖f (tr_k d g X.1)‖ₑ) fun X => meas_tr_k d hf X.1]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)
    ((lintegral_mono fun g => pt_bdd_k d g s (hK g).1 (hK g).2).trans (setLIntegral_const _ _).le)
theorem lint_fin_all_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD_k σ) {f : d.MxE → ℂ}
    (hf : f ∈ d.schM) :
    ∑' X, ∫⁻ g in d.D, ‖f (tr_k d g X)‖ₑ ∂d.μ ≠ ⊤ := by
  have := lint_fin_k hS d hf Set.univ
  rwa [tsum_univ (f := fun X => ∫⁻ g in d.D, ‖f (tr_k d g X)‖ₑ ∂d.μ)] at this
theorem continuous_tt_k (d : SD_k σ) : Continuous (d.tt) := by
  have h1 :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact h1.comp (continuous_finsetSum _ fun i _ => continuous_id.matrix_elem i i)
theorem thetaCoef_at_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : TBij_k) (hP : TPar_k) (hT : TTheta_k)
    (d : SD_k σ)
    {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {nb : d.nA_ → d.G} {lam : Measure d.nA_} {𝓖 : Set d.nA_}
    (hc : d.CD nb lam 𝓖) (T : d.nF_) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = d.orb T (d.om x Φ) := by
  have := countable_mat (E := E) d.m d.n
  have hΨ : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ hΦ
  have hf : d.T (d.om x Φ) ∈ d.schM := (hB F E σ d).1 _ hΨ
  have hen : ∀ a, ‖d.B.ψ a‖ₑ = 1 := fun a => by
    rw [← ofReal_norm, GlobalTheory.StdCharFromIsStd.norm_psi d.std, ENNReal.ofReal_one]
  have hψc : Continuous d.B.ψ := d.std.1
  set f : d.MxE → ℂ := d.T (d.om x Φ) with hfdef
  set c : ℝ := (d.μ.real d.D)⁻¹ with hcdef
  set G : d.ME → d.Mn :=
    fun X => d.gram (incM F X) (incM F X) with hG
  set e : d.nA_ → d.ME → ℂ :=
    fun β X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * G X))) with he
  set χ : d.nA_ → ℂ := fun β => d.B.ψ (-(d.tt (T.1.1 * β.1))) with hχ
  set H : d.ME → ℂ := fun X => ∫ g in d.D, f (tr_k d g X) ∂d.μ with hH
  have hmeas : ∀ X, AEStronglyMeasurable (fun g => f (tr_k d g X)) (d.μ.restrict d.D) :=
    fun X => (cont_tr_k d hf X).aestronglyMeasurable
  have hcb : Continuous fun β : d.nA_ => β.1 := continuous_subtypeVal
  have hec : ∀ X, Continuous fun β => e β X := fun X =>
    hψc.comp ((continuous_const.mul ((continuous_tt_k d).comp (hcb.matrix_mul continuous_const))).neg)
  have hχc : Continuous χ := hψc.comp (((continuous_tt_k d).comp (continuous_const.matrix_mul hcb)).neg)
  have hI : ∀ β, d.I Φ (nb β * x) = c • ∑' X, e β X * H X := fun β => by
    show thetaMean d.om d.S d.μ d.D Φ (nb β * x) = _
    rw [thetaMean, setAverage_eq]
    congr 1
    have hA' : ∀ g, thetaSum F (d.om (nb β * x) (d.S g Φ)) = ∑' X, e β X * f (tr_k d g X) :=
      fun g => stepA_k hP hT d hΦ hc.1 x β g
    simp only [hA']
    rw [integral_tsum (f := fun X g => e β X * f (tr_k d g X)) (fun X => (hmeas X).const_mul _) ?_]
    · exact tsum_congr fun X => integral_const_mul _ _
    · simpa only [he, eNorm_mul, hen, one_mul] using lint_fin_all_k hS d hf
  have hO : ∀ X, ∫ β in 𝓖, e β X * χ β ∂lam = if G X = (-2 : ℤ) • T.1.1 then 1 else 0 := fun X => by
    obtain ⟨hm, S₀, hS₀⟩ := gram_mem_k d X T
    simp only [he, hχ, chr_comb_k]
    rw [orth_k d hc _ hm ⟨S₀, hS₀⟩]
    simp only [half_eq_iff_k]
    rfl
  have h1 : ∀ β, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      c • ∑' X, e β X * χ β * H X := fun β => by
    rw [hI β, smul_mul_assoc, ← tsum_mul_right]
    congr 1
    exact tsum_congr fun X => by simp only [hχ, SD_k.tt]; ring
  have hlam : lam 𝓖 = 1 := hc.2.2.2
  have h2 : ∑' X, ∫⁻ β in 𝓖, ‖e β X * χ β * H X‖ₑ ∂lam ≠ ⊤ := by
    simp only [he, hχ, eNorm_mul, hen, one_mul, lintegral_const, Measure.restrict_apply_univ, hlam, mul_one]
    refine ne_top_of_le_ne_top (lint_fin_all_k hS d hf) (tsum_le_tsum fun X => ?_)
    exact eNorm_integral_le_lintegral_eNorm _
  have h3 : ∑' X, (if G X = (-2 : ℤ) • T.1.1 then (1 : ℂ) else 0) * H X =
      ∑' X : {X : d.ME // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, H X.1 := by
    show _ = ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (d.ME)), H X.1
    rw [tsum_subtype {X | G X = (-2 : ℤ) • T.1.1} H]
    exact tsum_congr fun X => by simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_mul, one_mul, zero_mul]
  have h4 : d.orb T (d.om x Φ) = c • ∑' X : {X : d.ME //
      d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, H X.1 := by
    have : Countable {X : d.ME // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} :=
      Subtype.countable
    show (⨍ g in d.D, ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (d.ME)),
      f (tr_k d g X.1) ∂d.μ) = c • ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (d.ME)), H X.1
    rw [setAverage_eq, integral_tsum (f := fun (X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m)
        (Fin d.n) E))) g =>
      f (tr_k d g X.1)) (fun X => hmeas X.1) (lint_fin_k hS d hf {X | G X = (-2 : ℤ) • T.1.1})]
  show ∫ β in 𝓖, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) ∂lam = _
  rw [integral_congr_ae (Eventually.of_forall h1), integral_smul,
    integral_tsum (f := fun X β => e β X * χ β * H X)
      (fun X => (((hec X).mul hχc).mul continuous_const).aestronglyMeasurable) h2, h4, ← h3]
  congr 1
  exact tsum_congr fun X => by rw [integral_mul_const, hO X]
theorem thetaCoef_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : TBij_k) (hP : TPar_k)
    (hT : TTheta_k) : ThetaCoef_k :=
  fun _ _ _ _ _ _ _ _ d _ hΦ _ _ _ hc T x => thetaCoef_at_k hS hB hP hT d hΦ hc T x
end Tauto
end PositivityTheory.SiegelWeilFormula
end
end
