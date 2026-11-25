module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfCells
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.IsFirstChernFamily
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ParsevalAdelicPairFundamental
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomainRationalPointsAdeleTupleFinitePoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariableStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralRationalPairFundDomainEqIteratedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodingerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvariStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParsevalFundamentalDomainThetaStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutProdA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

/-! # IndepDomK: Consolidated global theta-kernel definitions and proofs (IndepDomK). -/
@[expose] public section

noncomputable section

open GlobalTheory.Doubling (absE)
section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw
open GlobalTheory.ThK (incV)
open Matrix (fromBlocks fromBlocks_multiply fromBlocks_one single_apply transpose_one submatrix_apply)
open GlobalTheory.EisBL.DoubledParabolic (inFrame_mul inFrame_one)
open UpperTheory.TP.W (GoodK)
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.ParsevalPolarization
open GlobalTheory.ThetaTransform
theorem parseval_rational_pairing : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ
  : E →ₐ[F] E}
    {B : Base F E}, GoodK σ B → ∀ (N : ℕ),
    letI : MeasurableSpace (Fin N → AF F) := borel _
    letI : MeasurableSpace (VA F N) := borel _
    ∀ (ν : Measure (VA F N)), ν.IsAddHaarMeasure → ∀ 𝓕 : Set (VA F N),
      IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) 𝓕 ν →
      ∃ (μ : Measure (Fin N → AF F)) (c : ℝ), μ.IsAddHaarMeasure ∧ 0 < c ∧
        ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
          ∫ w in 𝓕, thV B.ψ Φ₁ w * starRingEnd ℂ (thV B.ψ Φ₂ w) ∂ν =
            (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μ := by
  intro F E _ _ _ _ _ σ B hB N
  let mA : MeasurableSpace (Fin N → AF F) := borel _
  let mV : MeasurableSpace (VA F N) := borel _
  intro ν hν 𝓕 h𝓕
  have : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  have : BorelSpace (Fin N → AF F) := ⟨rfl⟩
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).1
  let μ : Measure (Fin N → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.T.exists_fundDomain_rationalPointsAdeleTuple_finite_pos F (Fin N) μ hμ
  obtain ⟨c₁, hc0, hctop,
    hc⟩ := GlobalTheory.T.lintegral_rationalPair_fundDomain_eq_iterated F (Fin N) μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  set K : ENNReal := c₁ * μ 𝓕₁ with hK
  have hK0 : K ≠ 0 := mul_ne_zero hc0 h0
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top hctop htop
  have hpar : ∀ Φ ∈ schA F (Fin N), ∫⁻ w in 𝓕, ‖thV B.ψ Φ w‖ₑ ^ 2 ∂ν = K * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
    intro Φ hΦ
    have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F B.ψ hψ (Fin N) Φ hΦ
    have hG : @Measurable _ _ (borel _) _ (fun w : (Fin N → AF F) × (Fin N → AF F) =>
        ‖thetaSum F (schr B.ψ w Φ)‖ₑ ^ 2) := Measurable.pow_const
          (measurable_eNorm.comp hm) 2
    show ∫⁻ w in 𝓕, ‖thetaSum F (schr B.ψ w Φ)‖ₑ ^ 2 ∂ν = _
    rw [hc _ hG (fun γ hγ w => by
      rw [← ofReal_norm, ← ofReal_norm,
        GlobalTheory.T.norm_adelicThetaSum_schroedinger_rationalPair_invariant F B.ψ hψ (Fin N) Φ γ hγ w])]
    simp_rw [GlobalTheory.T.lintegral_adelicThetaSum_sq_parseval_second_variable F B.ψ hψ (Fin N) μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ]
    rw [lintegral_const_mul' _ _ htop, GlobalTheory.T.parseval_fundamental_domain_theta F (Fin N) μ hμ 𝓕₁ h𝓕₁ Φ hΦ, hK,
      mul_assoc]
  have henorm : ∀ z : ℂ, ‖‖z‖ ^ 2‖ₑ = ‖z‖ₑ ^ 2 := fun z => by
    rw [Real.eNorm_eq_ofReal (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hΦint : ∀ Φ ∈ schA F (Fin N), Integrable (fun x => ‖Φ x‖ ^ 2) μ := fun Φ hΦ =>
    (schA_memLp_two F (Fin N) μ hμ Φ hΦ).integrable_norm_pow two_ne_zero
  have hthint : ∀ Φ ∈ schA F (Fin N), Integrable (fun w => ‖thV B.ψ Φ w‖ ^ 2) (ν.restrict 𝓕) := by
    intro Φ hΦ
    have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F B.ψ hψ (Fin N) Φ hΦ
    refine ⟨((hm.norm.pow_const 2).aestronglyMeasurable), ?_⟩
    show ∫⁻ w in 𝓕, ‖‖thV B.ψ Φ w‖ ^ 2‖ₑ ∂ν < ⊤
    simp_rw [henorm]
    rw [hpar Φ hΦ]
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hKt) ?_
    have := (hΦint Φ hΦ).2
    unfold HasFiniteIntegral at this
    simp_rw [henorm] at this
    exact this
  have hreal : ∀ Φ ∈ schA F (Fin N), ∫ w in 𝓕, ‖thV B.ψ Φ w‖ ^ 2 ∂ν = K.toReal * ∫ x, ‖Φ x‖ ^ 2 ∂μ := by
    intro Φ hΦ
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
        (hthint Φ hΦ).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) (hΦint Φ hΦ).aestronglyMeasurable]
    have e1 : ∀ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    simp_rw [e1]
    rw [hpar Φ hΦ, ENNReal.toReal_mul]
  refine ⟨μ, K.toReal, hμ, ENNReal.toReal_pos hK0 hKt, fun Φ₁ hΦ₁ Φ₂ hΦ₂ => ?_⟩
  have hmem : ∀ a : ℂ, Φ₁ + a • Φ₂ ∈ schA F (Fin N) := fun a => add_mem hΦ₁ (Submodule.smul_mem _ a hΦ₂)
  have hth : ∀ a : ℂ, thV B.ψ (Φ₁ + a • Φ₂) = fun w => thV B.ψ Φ₁ w + a * thV B.ψ Φ₂ w := by
    intro a
    rw [thV_add hR hψ (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ₁ hΦ₁)
      (GlobalTheory.SchwartzDecay.decay_smul a (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ₂ hΦ₂)),
      thV_smul]
    rfl
  have hfn : ∀ a : ℂ, (Φ₁ + a • Φ₂) = fun x => Φ₁ x + a * Φ₂ x := fun a => rfl
  refine polar μ (ν.restrict 𝓕) Φ₁ Φ₂ (thV B.ψ Φ₁) (thV B.ψ Φ₂) K.toReal (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · have := hΦint _ (hmem a)
    rwa [hfn a] at this
  · have := hthint _ (hmem a)
    rwa [hth a] at this
  · have := hreal _ (hmem a)
    rwa [hth a, hfn a] at this
end PositivityTheory.ThKW.ParsevalPolarization
end
end

section
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def Au_k {d : SD_k σ} (L : LD_k d) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)
theorem em_ne_k {d : SD_k σ} (L : LD_k d) (j : Fin L.n) : L.em j ≠ L.i₀ := fun h => (L.rng (L.em j)).2 ⟨j, rfl⟩ h
theorem Au_mul_k {d : SD_k σ} (L : LD_k d) (u v : Fin L.n → AE F E) : Au_k L u * Au_k L v = Au_k L (u + v) := by
  have h0 : (∑ j, Matrix.single L.i₀ (L.em j) (u j)) * (∑ k, Matrix.single L.i₀ (L.em k) (v k)) = 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_eq_zero fun k _ => Matrix.single_mul_single_of_ne _ _ _ _ (em_ne_k L j) _
  simp only [Au_k, add_mul, mul_add, one_mul, mul_one, h0, add_zero, Pi.add_apply, Matrix.single_add,
    Finset.sum_add_distrib, add_assoc]
theorem Au_zero_k {d : SD_k σ} (L : LD_k d) : Au_k L 0 = 1 := by simp [Au_k]
theorem cA_injective_k (d : SD_k σ) : Function.Injective (cA σ) := by
  have := Module.Finite.of_basis d.bs
  have hb := AlgHom.bijective σ
  exact (Algebra.TensorProduct.congr AlgEquiv.refl (AlgEquiv.ofBijective σ hb)).injective
theorem frame_blk_k (d : SD_k σ) {x : d.G} {A A' : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (h : inFrame d.b x = fromBlocks A 0 0 A') : Aᵀ * A'.map (cA σ) = 1 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have h2 := kunf.frame_eq hε x
  rw [h] at h2
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.mul_one,
    Matrix.map_zero _ (map_zero (cA σ))] at h2
  exact (Matrix.fromBlocks_inj.1 h2).2.1
theorem blk_unique_k (d : SD_k σ) {x y : d.G} {A A₁ A₂ : Matrix (Fin d.n) (Fin d.n) (AE F E)}
    (hx : inFrame d.b x = fromBlocks A 0 0 A₁) (hy : inFrame d.b y = fromBlocks A 0 0 A₂) : x = y := by
  have h1 := frame_blk_k d hx
  have h2 := frame_blk_k d hy
  have h1' : A₁.map (cA σ) * Aᵀ = 1 := mul_eq_one_comm.1 h1
  have e : A₁.map (cA σ) = A₂.map (cA σ) := by
    calc A₁.map (cA σ) = A₁.map (cA σ) * (Aᵀ * A₂.map (cA σ)) := by rw [h2, Matrix.mul_one]
      _ = A₂.map (cA σ) := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
  have e2 : A₁ = A₂ := Matrix.map_injective (cA_injective_k d) e
  apply kunf.inFrame_injective d.b
  rw [hx, hy, e2]
end PositivityTheory.SiegelWeilFormula.Act.C1
end

section
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD_k σ} {L : LD_k d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n
  → AE F E)} {nb : nA σ d.Y d.b → d.G}
def Ap_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : Matrix (Fin d.n) (Fin d.n) (AE F E) := (hU.1 u).choose
theorem inFrame_uM_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) :
    inFrame d.b (uM u) = fromBlocks (Au_k L u) 0 0 (Ap_k hU u) := (hU.1 u).choose_spec
theorem uM_add_k (hU : L.UData uM ν 𝓤) (u v : Fin L.n → AE F E) : uM (u + v) = uM u * uM v := by
  refine blk_unique_k d (A₂ := Ap_k hU u * Ap_k hU v) (inFrame_uM_k hU (u + v)) ?_
  rw [inFrame_mul, inFrame_uM_k hU, inFrame_uM_k hU, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Au_mul_k]
theorem uM_zero_k (hU : L.UData uM ν 𝓤) : uM 0 = 1 := by
  refine blk_unique_k d (A₂ := 1) (inFrame_uM_k hU 0) ?_
  rw [inFrame_one, Au_zero_k, fromBlocks_one]
theorem uM_neg_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : uM (-u) = (uM u)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← uM_add_k hU, neg_add_cancel, uM_zero_k hU])
theorem Ap_neg_mul_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : Ap_k hU (-u) * Ap_k hU u = 1 := by
  have h := congrArg (inFrame d.b) (show uM (-u) * uM u = 1 by rw [← uM_add_k hU, neg_add_cancel, uM_zero_k hU])
  rw [inFrame_mul, inFrame_uM_k hU, inFrame_uM_k hU, fromBlocks_multiply,
    inFrame_one, ← fromBlocks_one] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
  exact (Matrix.fromBlocks_inj.1 h).2.2.2
theorem frame_conj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    inFrame d.b ((uM u)⁻¹ * nb β * uM u) = fromBlocks 1 (Au_k L (-u) * β.1 * Ap_k hU u) 0 1 := by
  rw [inFrame_mul, inFrame_mul, ← uM_neg_k hU,
    inFrame_uM_k hU, inFrame_uM_k hU, hN β,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Au_mul_k, neg_add_cancel, Au_zero_k,
    Ap_neg_mul_k hU]
theorem cj_mem_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Au_k L (-u) * β.1 * Ap_k hU u ∈ nA σ d.Y d.b :=
  AddSubgroup.subset_closure ⟨_, frame_conj_k hU hN u β⟩
def cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b →+ nA σ d.Y d.b where
  toFun β := ⟨_, cj_mem_k hU hN u β⟩
  map_zero' := Subtype.ext (by simp)
  map_add' β β' := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
theorem cj_val_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    (cj_k hU hN u β).1 = Au_k L (-u) * β.1 * Ap_k hU u := rfl
theorem nb_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    nb (cj_k hU hN u β) = (uM u)⁻¹ * nb β * uM u := by
  apply kunf.inFrame_injective d.b
  rw [frame_conj_k hU hN, hN]
  rfl
theorem cj_inv_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    cj_k hU hN (-u) (cj_k hU hN u β) = β := by
  apply Subtype.ext
  have h1 : Au_k L u * Au_k L (-u) = 1 := by rw [Au_mul_k, add_neg_cancel, Au_zero_k]
  have h2 : Ap_k hU u * Ap_k hU (-u) = 1 := by simpa using Ap_neg_mul_k hU (-u)
  rw [cj_val_k, cj_val_k, neg_neg]
  calc Au_k L u * (Au_k L (-u) * β.1 * Ap_k hU u) * Ap_k hU (-u)
      = (Au_k L u * Au_k L (-u)) * β.1 * (Ap_k hU u * Ap_k hU (-u)) := by simp only [Matrix.mul_assoc]
    _ = β.1 := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
theorem continuous_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) :
    Continuous (cj_k hU hN u) :=
  ((continuous_const.matrix_mul continuous_subtypeVal).matrix_mul continuous_const).subtype_mk _
def cjE_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) (u : Fin L.n → AE F E) : nA σ d.Y d.b ≃ₜ+ nA σ d.Y d.b where
  toFun := cj_k hU hN u
  invFun := cj_k hU hN (-u)
  left_inv β := cj_inv_k hU hN u β
  right_inv β := by simpa using cj_inv_k hU hN (-u) β
  map_add' := map_add _
  continuous_toFun := continuous_cj_k hU hN u
  continuous_invFun := continuous_cj_k hU hN (-u)
end PositivityTheory.SiegelWeilFormula.Act.C1
end

section
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem phz_leftInv_k (d : SD_k σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ d.Y ⊓ rat2 σ d.Y)
      (phz_k d f s₁ z) := by
  intro p hp g
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 hp.1
  obtain ⟨T, hT⟩ := par_rat ht hp.2
  obtain ⟨u, hu⟩ := det_rat hT
  have ha : d.a (p * g) = d.a g := by
    rw [IsHgt.mul d.ok.hgt ht, hu, GlobalTheory.Doubling.absE_inclR]; simp
  have hfp := Law.rat (z := s₁ + (d.n : ℂ) / 2) hf.law d.ok.hecke hp.1 hp.2 g
  simp only [phz_k, SD_k.Ht, ha, hfp]
theorem eis_leftInv_k (d : SD_k σ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) :
    ∀ γ ∈ rat2 σ d.Y, ∀ g, d.eis f s₁ z (γ * g) = d.eis f s₁ z g :=
  GlobalTheory.Eis.leftInv_cosetSum (phz_leftInv_k d hf z)
theorem fc_dom_k (d : SD_k σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 𝓖₀ : Set (nA σ d.Y d.b)}
    (h : CoefData (Y := d.Y) d.b nb lam 𝓖) (h₀ : CoefData (Y := d.Y) d.b nb lam 𝓖₀)
    (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T g = fc d.B.ψ d.b nb lam 𝓖₀ φ T g := by
  unfold fc
  have : lam.IsAddHaarMeasure := h.2.1
  have : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  have hfd : IsAddFundamentalDomain (nF σ d.Y d.b) 𝓖 lam := h.2.2.1
  have hfd₀ : IsAddFundamentalDomain (nF σ d.Y d.b) 𝓖₀ lam := h₀.2.2.1
  refine hfd.setIntegral_eq hfd₀ fun β₀ β => ?_
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add h.1, mul_assoc, hφ _ (kunf.nb_rat h.1 β₀.2), e2, Matrix.mul_add, Matrix.trace_add,
    map_add (f := _), neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]
end PositivityTheory.SiegelWeilFormula.Act.C1
end

section
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD_k σ} {L : LD_k d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n
  → AE F E)} {nb : nA σ d.Y d.b → d.G}
theorem ratV_inc_k {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : ∃ v : Fin L.n → E, u = incV F v := by
  induction hu using AddSubgroup.closure_induction with
  | mem _ h => obtain ⟨v, rfl⟩ := h; exact ⟨v, rfl⟩
  | zero => exact ⟨0, funext fun i => by simp [incV]⟩
  | add _ _ _ _ h h' =>
    obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := h'; exact ⟨v + w, funext fun i => by simp [incV]⟩
  | neg _ _ h => obtain ⟨v, rfl⟩ := h; exact ⟨-v, funext fun i => by simp [incV]⟩
theorem neg_incV_k (v : Fin L.n → E) : -incV F v = incV F (-v) := funext fun i =>
  by simp [incV]
def unipotentFirstMatrix (L : LD_k d) (v : Fin L.n → E) : Matrix (Fin d.n) (Fin d.n) E := 1 + ∑ j,
  Matrix.single L.i₀ (L.em j) (v j)
theorem Au_inc_k (v : Fin L.n → E) : Au_k L (incV F v) = incM F (unipotentFirstMatrix L v) := by
  ext a b
  simp [Au_k, unipotentFirstMatrix, incM, Matrix.one_apply, Matrix.sum_apply, single_apply,
    incV, map_sum, apply_ite]
theorem Apc_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : (Ap_k hU u).map (cA σ) = (Au_k L (-u))ᵀ := by
  have h1 := mul_eq_one_comm.1 (frame_blk_k d (inFrame_uM_k hU u))
  have h2 : (Au_k L u)ᵀ * (Au_k L (-u))ᵀ = 1 :=
    by rw [← Matrix.transpose_mul, Au_mul_k, neg_add_cancel, Au_zero_k, transpose_one]
  calc (Ap_k hU u).map (cA σ) = (Ap_k hU u).map (cA σ) * ((Au_k L u)ᵀ * (Au_k L (-u))ᵀ) := by rw [h2, Matrix.mul_one]
    _ = (Au_k L (-u))ᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
theorem Ap_inc_k (hU : L.UData uM ν 𝓤) (v : Fin L.n → E) : ∃ M : Matrix (Fin d.n) (Fin d.n) E,
    Ap_k hU (incV F v) = incM F M := by
  have := Module.Finite.of_basis d.bs
  let e := AlgEquiv.ofBijective σ (AlgHom.bijective σ)
  refine ⟨((unipotentFirstMatrix L (-v))ᵀ).map e.symm, Matrix.map_injective (cA_injective_k d) ?_⟩
  show (Ap_k hU (incV F v)).map (cA σ) = (incM F (((unipotentFirstMatrix L (-v))ᵀ).map e.symm)).map (cA
    σ)
  rw [Apc_k, kunf.incM_map_cA, Matrix.map_map, neg_incV_k, Au_inc_k]
  have h : (⇑σ ∘ ⇑e.symm) = id := funext fun x => e.apply_symm_apply x
  rw [h, Matrix.map_id]
  rfl
theorem uM_rat_k (hU : L.UData uM ν 𝓤) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : uM u ∈ rat2 σ d.Y := by
  obtain ⟨v, rfl⟩ := ratV_inc_k hu
  obtain ⟨M, hM⟩ := Ap_inc_k hU v
  refine kunf.rat_of_inFrame (b := d.b) (M := fromBlocks (unipotentFirstMatrix L v) 0 0 M) ?_
  rw [inFrame_uM_k hU, Au_inc_k, hM]
  simp [incM, Matrix.fromBlocks_map]
theorem cj_rat_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV)
    {β : nA σ d.Y d.b} (hβ : β ∈ nF σ d.Y d.b) : cj_k hU hN u β ∈ nF σ d.Y d.b := by
  obtain ⟨v, rfl⟩ := ratV_inc_k hu
  obtain ⟨M, hM⟩ := Ap_inc_k hU v
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 hβ
  refine kunf.mem_nF_iff.2 ⟨unipotentFirstMatrix L (-v) * T * M, ?_⟩
  rw [cj_val_k, neg_incV_k, Au_inc_k, hT, hM, kunf.incM_mul', kunf.incM_mul']
theorem mul_Au_k (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ a, X a L.i₀ = 0) (u : Fin L.n → AE F E) :
    X * Au_k L u = X := by
  have h : ∀ j, X * Matrix.single L.i₀ (L.em j) (u j) = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, zero_mul]
    · exact mul_zero _
  simp only [Au_k, Matrix.mul_add, Matrix.mul_one, Finset.mul_sum, h, Finset.sum_const_zero, add_zero]
theorem AuT_mul_k (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ b, X L.i₀ b = 0) (u : Fin L.n → AE F E) :
    (Au_k L u)ᵀ * X = X := by
  have h : ∀ j, (Matrix.single L.i₀ (L.em j) (u j))ᵀ * X = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, mul_zero]
    · exact zero_mul _
  simp only [Au_k, Matrix.transpose_add, transpose_one, Matrix.transpose_sum, Matrix.add_mul, Matrix.one_mul,
    Finset.sum_mul, h, Finset.sum_const_zero, add_zero]
theorem trace_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Matrix.trace (T.1.1 * (cj_k hU hN u β).1) = Matrix.trace (T.1.1 * β.1) := by
  have h1 : T.1.1 * Au_k L (-u) = T.1.1 := mul_Au_k _ (fun a => (hT.1 a).2) _
  have h2 : Ap_k hU u * T.1.1 = T.1.1 := by
    apply Matrix.map_injective (cA_injective_k d)
    show (Ap_k hU u * T.1.1).map (cA σ) = T.1.1.map (cA σ)
    rw [kunf.map_cA_mul, Apc_k]
    exact AuT_mul_k _ (fun b => by simp [(hT.1 b).1]) _
  rw [cj_val_k, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2]
end PositivityTheory.SiegelWeilFormula.Act.C1
end

section
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD_k σ}
theorem range_or_k (L : LD_k d) (u : Fin d.n ⊕ Fin d.n) :
    (∃ u', Sum.map L.em L.em u' = u) ∨ u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases u with a | a <;>
  · by_cases ha : a = L.i₀
    · right; simp [ha]
    · obtain ⟨a', rfl⟩ := (L.rng a).1 ha
      left; first | exact ⟨Sum.inl a', rfl⟩ | exact ⟨Sum.inr a', rfl⟩
theorem j_par_k (L : LD_k d) {p : G2 σ L.Y} (hp : p ∈ par2 σ L.Y) : L.j p ∈ par2 σ d.Y := by
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame]
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.sd.ok.frame] at hp
  ext a c
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  rcases range_or_k L (Sum.inr a) with ⟨u', hu'⟩ | hu
  · rcases range_or_k L (Sum.inl c) with ⟨v', hv'⟩ | hv
    · rcases u' with a' | a'
      · simp at hu'
      rcases v' with c' | c'
      · have h1 := congrFun (congrFun (L.j_in p) (Sum.inr a')) (Sum.inl c')
        simp only [submatrix_apply, Sum.map_inr, Sum.map_inl] at h1
        simp only [Sum.map_inr, Sum.inr.injEq] at hu'
        simp only [Sum.map_inl, Sum.inl.injEq] at hv'
        rw [← hu', ← hv', h1]
        exact congrFun (congrFun hp a') c'
      · simp at hv'
    · rw [(L.j_out p _ hv (Sum.inr a)).2]
      simp
  · rw [(L.j_out p _ hu (Sum.inl c)).1]
    simp
theorem j_rat_k (L : LD_k d) {p : G2 σ L.Y} (hp : p ∈ rat2 σ L.Y) : L.j p ∈ rat2 σ d.Y := by
  obtain ⟨g, hg⟩ := hp
  have hm : mat2 p = incM F g.1 := (congrArg Units.val hg).symm
  have hL : inFrame L.b p = incM F ((L.b⁻¹).1 * g.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]; rfl
  let M' := (L.b⁻¹).1 * g.1 * L.b.1
  let M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := fun u v =>
    if hu : ∃ u', Sum.map L.em L.em u' = u then
      if hv : ∃ v', Sum.map L.em L.em v' = v then M' hu.choose hv.choose else (1 : Matrix _ _ E) u v
    else (1 : Matrix _ _ E) u v
  refine kunf.rat_of_inFrame (b := d.b) (M := M) ?_
  ext u v
  show inFrame d.b (L.j p) u v = inclR (F := F) (AF F) (M u v)
  dsimp only [M]
  by_cases hu : ∃ u', Sum.map L.em L.em u' = u
  · by_cases hv : ∃ v', Sum.map L.em L.em v' = v
    · rw [dite_eq_left hu, dite_eq_left hv]
      have h1 := congrFun (congrFun (L.j_in p) hu.choose) hv.choose
      simp only [submatrix_apply, hu.choose_spec, hv.choose_spec] at h1
      rw [h1, hL]
      rfl
    · rw [dite_eq_left hu, dite_eq_right hv]
      have hv' := (range_or_k L v).resolve_left hv
      rw [(L.j_out p _ hv' u).2]
      simp [Matrix.one_apply, apply_ite]
  · rw [dite_eq_right hu]
    have hu' := (range_or_k L u).resolve_left hu
    rw [(L.j_out p _ hu' v).1]
    simp [Matrix.one_apply, apply_ite]
theorem phz_j_leftInv_k (L : LD_k d) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) (x : d.G) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ L.Y ⊓ rat2 σ L.Y)
      (fun g : G2 σ L.Y => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) := by
  intro p hp g
  show phz_k d f s₁ z (L.j (p * g) * x) =
    phz_k d f s₁ z (L.j g * x)
  rw [map_mul, mul_assoc]
  exact phz_leftInv_k d hf z (L.j p) ⟨j_par_k L hp.1, j_rat_k L hp.2⟩ _
end PositivityTheory.SiegelWeilFormula.Act.C1
end

section
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isClosed_nA_k (d : SD_k σ) : IsClosed (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hc := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have e : (nA σ d.Y d.b : Set (Matrix (Fin d.n) (Fin d.n) (AE F E))) =
      {β | βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ))} := Set.ext fun β => kunf.mem_nA_iff hε β
  rw [e]
  exact isClosed_eq continuous_id.matrix_transpose (((continuous_id.matrix_map hc).const_smul (((ε : ℤ) : AE F E))).neg)
instance locCompact_nA_k (d : SD_k σ) : LocallyCompactSpace (nA σ d.Y d.b) :=
  have : LocallyCompactSpace (Matrix (Fin d.n) (Fin d.n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin d.n → Fin d.n → AE F E))
  (isClosed_nA_k d).isClosedEmbedding_subtypeVal.locallyCompactSpace
theorem coef_periodic_k (d : SD_k σ) {nb : nA σ d.Y d.b → d.G} (hN : IsNMap d.b nb) (φ : d.G → ℂ)
    (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) (T : nF σ d.Y d.b) (g : d.G) (β₀ : nF σ d.Y d.b)
    (β : nA σ d.Y d.b) :
    φ (nb (β₀ +ᵥ β) * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * (β₀ +ᵥ β).1)))) =
      φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) := by
  have e1 : (β₀ +ᵥ β : nA σ d.Y d.b) = β₀.1 + β := rfl
  have e2 : ((β₀.1 + β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E)) = β₀.1.1 + β.1 := rfl
  rw [e1, kunf.nb_add hN, mul_assoc, hφ _ (kunf.nb_rat hN β₀.2), e2, Matrix.mul_add, Matrix.trace_add, map_add (f := _),
    neg_add,
    AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, kunf.psi_rat d.ok.good.std T β₀, inv_one, one_mul]
variable {d : SD_k σ} {L : LD_k d}
theorem cj_mp_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) {v : Fin L.n → AE F E} (hv : v ∈ L.ratV) :
    MeasurePreserving (cj_k hU h.1 v) lam lam := by
  have : lam.IsAddHaarMeasure := h.2.1
  refine ⟨(continuous_cj_k hU h.1 v).measurable, ?_⟩
  have hl := latHaar (nA σ d.Y d.b) lam (nF σ d.Y d.b) (cjE_k hU h.1 v) (fun x => ⟨fun hx => ?_,
    fun hx => cj_rat_k hU h.1 hv hx⟩)
    𝓖 h.2.2.1 (by erw [h.2.2.2]; exact one_ne_zero) (by erw [h.2.2.2]; exact ENNReal.one_ne_top)
  · exact hl
  · have := cj_rat_k hU h.1 (neg_mem hv) hx
    rwa [show cj_k hU h.1 (-v) (cjE_k hU h.1 v x) = x from cj_inv_k hU h.1 v x] at this
theorem fc_conj_k {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (φ : d.G → ℂ) (hφ : ∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g)
    {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) (g : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * g) = fc d.B.ψ d.b nb lam 𝓖 φ T g := by
  have : lam.IsAddHaarMeasure := h.2.1
  have : VAddInvariantMeasure (nF σ d.Y d.b) (nA σ d.Y d.b) lam := ⟨fun c s _ => measure_preimage_add lam c.1 s⟩
  let H : nA σ d.Y d.b → ℂ := fun β =>
    φ (nb β * g) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
  have e1 : ∀ β, φ (nb β * (uM u * g)) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      H (cj_k hU h.1 u β) := by
    intro β
    have e : nb β * (uM u * g) = uM u * (nb (cj_k hU h.1 u β) * g) := by rw [nb_cj_k hU h.1 u β]; group
    simp only [H]
    rw [e, hφ _ (uM_rat_k hU hu), trace_cj_k hU h.1 hT]
  have hme := (cjE_k hU h.1 u).toHomeomorph.measurableEmbedding
  have himg : (cj_k hU h.1 u) '' 𝓖 = (cj_k hU h.1 (-u)) ⁻¹' 𝓖 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show cj_k hU h.1 (-u) (cj_k hU h.1 u x) ∈ 𝓖
      rwa [cj_inv_k]
    · intro hy
      refine ⟨cj_k hU h.1 (-u) y, hy, ?_⟩
      simpa using cj_inv_k hU h.1 (-u) y
  have hfd : IsAddFundamentalDomain (nF σ d.Y d.b) ((cj_k hU h.1 (-u)) ⁻¹' 𝓖) lam := by
    refine h.2.2.1.preimage_of_equiv (cj_mp_k h hU (neg_mem hu)).quasiMeasurePreserving
      (e := fun γ => ⟨cj_k hU h.1 u γ.1, cj_rat_k hU h.1 hu γ.2⟩) ⟨fun γ γ' hγ => ?_, fun γ => ?_⟩ fun γ x => ?_
    · have := congrArg (fun y : nF σ d.Y d.b => cj_k hU h.1 (-u) y.1) hγ
      simp only [cj_inv_k] at this
      exact Subtype.ext this
    · refine ⟨⟨cj_k hU h.1 (-u) γ.1, cj_rat_k hU h.1 (neg_mem hu) γ.2⟩, Subtype.ext ?_⟩
      simpa using cj_inv_k hU h.1 (-u) γ.1
    · show cj_k hU h.1 (-u) ((cj_k hU h.1 u γ.1) + x) = γ.1 + cj_k hU h.1 (-u) x
      rw [map_add (f := _), cj_inv_k]
  unfold fc
  simp_rw [e1]
  erw [← (cj_mp_k h hU hu).setIntegral_image_emb hme H 𝓖]
  rw [himg]
  exact hfd.setIntegral_eq h.2.2.1 (fun β₀ β => coef_periodic_k d h.1 φ hφ T g β₀ β)
end PositivityTheory.SiegelWeilFormula.Act.C1
end

namespace PositivityTheory.SiegelWeilFormula.Act
theorem indepDom_k : IndepDom_k := by
  intro F E _ _ _ _ _ σ d L s₁ f hf z
  have hE := C1.eis_leftInv_k d hf z
  refine ⟨fun nb lam 𝓖 𝓖₀ h h₀ uM ν 𝓤 𝓤₀ hU hU₀ T T' hT x => ?_, fun nb' lam' 𝓖' 𝓖'₀ h' h'₀ T' x => ?_⟩
  · have step1 : ∀ g, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T g = fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T g :=
      fun g => C1.fc_dom_k d h h₀ _ hE T g
    simp_rw [step1]
    have := hU.2.1
    have : VAddInvariantMeasure L.ratV (Fin L.n → AE F E) ν := ⟨fun c s _ => measure_preimage_add ν c.1 s⟩
    have : Countable L.ratV := by
      have := (Module.finBasis ℚ E).equivFun.injective.countable
      refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
        (⟨incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
      obtain ⟨v, hv⟩ := C1.ratV_inc_k u.2
      exact ⟨v, Subtype.ext hv.symm⟩
    refine hU.2.2.1.setIntegral_eq hU₀.2.2.1 fun u₀ u => ?_
    show fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM (u₀.1 + u) * x) = fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM u *
      x)
    rw [C1.uM_add_k hU, mul_assoc, C1.fc_conj_k h₀ hU _ hE hT u₀.2]
  · exact C1.fc_dom_k L.sd h' h'₀ _ (GlobalTheory.Eis.leftInv_cosetSum (C1.phz_j_leftInv_k L hf z x)) T' 1
end PositivityTheory.SiegelWeilFormula.Act
end
end
