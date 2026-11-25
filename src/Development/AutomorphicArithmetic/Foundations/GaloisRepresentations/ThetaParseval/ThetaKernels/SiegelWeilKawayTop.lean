module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIntertwine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierTransformMatrixSpaceInvolution
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLinearChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzQuadraticPhaseMultiplication
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.AwStep
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.DecAlg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.FinBase
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.FinTop
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.Imports
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.InFrameInvOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.ContAdm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.EqZeroOfEvalReal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.GoodSigPq
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LongWeylFunctional
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Assemble
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocForm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocNbar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocalOperatorLongWeylIntegral
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.PsiZeroGram
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNB
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.SigmaSigma
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.POfAddQOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Decomp
public import Development.WeilBound.ThetaLifts.LatticeBasics.ConstIdele

/-! # SiegelWeilKawayTop: Consolidated global theta-kernel definitions and proofs (SiegelWeilKawayTop). -/
@[expose] public section
noncomputable section
open scoped TensorProduct NNReal Classical SchwartzMap Matrix
open GlobalTheory.Doubling (absE)
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU
  GlobalTheory.LFun Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open Matrix (fromBlocks fromBlocks_multiply fromBlocks_map fromBlocks_transpose fromBlocks_smul fromBlocks_one
  fromBlocks_inj transpose_map transpose_mul transpose_one conjTranspose_smul conjTranspose_mul conjTranspose_apply
  conjTranspose_one conjTranspose_conjTranspose trace_add trace_zero trace_smul det_smul det_one)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD_k
open RD
section ExplicitW
variable {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F)
private theorem psi_nU (b : d.Mnc) (hb : bᴴ = b) (β : d.Mn) (hβw : d.cw w β = R.ζ • b)
    (hβo : ∀ w', w' ≠ w → d.cw w' β = 0) (hβf : finOne F • β = 0) (X : d.MxE) :
    d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) = Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (b * ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X)))) := by
  have hζ0 := Krd.zeta_ne R.hζ; set z : AE F E := (-(⅟(2 : AF F))) • (β * d.gram X X).trace with hz
  have e1 : -(⅟(2 : AF F) * d.tt (β * d.gram X X)) = Algebra.trace (AF F) (AE F E) z := by
    rw [hz, LinearMap.map_smul, smul_eq_mul, neg_mul]; rfl
  have hpi (w') : piInf (d.B.emb w') z = -(1 / 2) * (d.cw w' β * d.cw w' (d.gram X X)).trace := by
    rw [hz, Algebra.smul_def, map_mul, map_neg, map_neg, piInf_half, ← Krd.cw_mul_k]
    congr 1; simp only [Matrix.trace, SD_k.cw, Matrix.map_apply, Matrix.diag, map_sum]
  have hf : finOne F • z = 0 := by
    rw [hz, smul_comm, ← trace_smul, ← Matrix.smul_mul, hβf, Matrix.zero_mul, trace_zero, smul_zero]
  have ho (u) (hu : u ≠ w) : piInf (d.B.emb u) z = 0 := by
    rw [hpi, hβo u hu, Matrix.zero_mul, trace_zero, mul_zero]
  rw [e1, Place.psi_trace_at d.std d.cm d.B.emb w z hf ho, hpi, hβw, R.cw_gram w X]
  set T := (b * ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X))).trace with hT
  have hreal : ((T.re : ℝ) : ℂ) = T := trace_herm_real _ _ hb (by rw [conjTranspose_mul, conjTranspose_conjTranspose])
  have e2 : (R.ζ • b * (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X))).trace =
      ((R.sg w : ℤ) : ℂ) * T := by
    rw [smul_mul_smul_comm, trace_smul, hT, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]
  rw [e2, ← hreal]; congr 1; push_cast
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re,
    Complex.intCast_im, mul_zero, sub_zero, Complex.div_ofNat_re, Complex.one_re, Complex.neg_im, Complex.div_ofNat_im,
    Complex.one_im]
  push_cast; ring
private theorem stepM_gen (hT : TAll_k) (y : GR d.n) (a : d.Mnc) (ha : IsUnit a.det) (hy : mR y = mLoc a) :
    ∃ t : d.Gn, d.cw w t.1 = a ∧ (∀ w', w' ≠ w → d.cw w' t.1 = 1) ∧ finOne F • t.1 = finOne F • 1 ∧
      R.StepOK w (R.ι w y) (fun f u => ((d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
        (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ)) * f (Matrix.of u * a)) id := by
  have haH : IsUnit aᴴ.det := by rw [Matrix.det_conjTranspose]; exact ha.star
  have hyi : mR y⁻¹ = fromBlocks a⁻¹ 0 0 aᴴ := by
    have h1 : mR y * mR y⁻¹ = 1 := by
      show ((y * y⁻¹ : GR d.n) : GL (Fin d.n ⊕ Fin d.n) ℂ).1 = 1; rw [mul_inv_cancel]; rfl
    have h2 : fromBlocks a⁻¹ 0 0 aᴴ * mR y = 1 := by
      rw [hy, mLoc, fromBlocks_multiply, ← fromBlocks_one]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.nonsing_inv_mul _ ha,
        Matrix.mul_nonsing_inv _ haH]
    exact (left_inv_eq_right_inv h2 h1).symm
  obtain ⟨hM, hA1, -, hO1, hF1, -⟩ := R.frame_diag w y a (aᴴ)⁻¹ hy
  obtain ⟨hM', -, hD', hO', -, hF'⟩ := R.frame_diag w y⁻¹ a⁻¹ aᴴ hyi
  set M := inFrame d.b (R.ι w y); set M' := inFrame d.b (R.ι w y⁻¹)
  have hMM : M * M' = 1 := by rw [← d.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, d.inFrame_one]
  have hMM' : M' * M = 1 := by rw [← d.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, d.inFrame_one]
  have bl {P Q : d.Mn2} (hP : P = fromBlocks P.toBlocks₁₁ 0 0 P.toBlocks₂₂)
      (hQ : Q = fromBlocks Q.toBlocks₁₁ 0 0 Q.toBlocks₂₂) (hPQ : P * Q = 1) :
      P.toBlocks₁₁ * Q.toBlocks₁₁ = 1 ∧ P.toBlocks₂₂ * Q.toBlocks₂₂ = 1 := by
    rw [hP, hQ, fromBlocks_multiply, ← fromBlocks_one] at hPQ
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hPQ
    exact ⟨(fromBlocks_inj.mp hPQ).1, (fromBlocks_inj.mp hPQ).2.2.2⟩
  obtain ⟨t1, u1⟩ := bl hM hM' hMM; obtain ⟨t2, u2⟩ := bl hM' hM hMM'
  let t : d.Gn := ⟨M.toBlocks₁₁, M'.toBlocks₁₁, t1, t2⟩; let u : d.Gn := ⟨M.toBlocks₂₂, M'.toBlocks₂₂, u1, u2⟩
  refine ⟨t, hA1, fun w' h => (hO1 w' h).1, hF1, fun f ⟨φ, hφ⟩ => by
    subst hφ; exact _root_.GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul d.m d.n _ a ha φ,
    fun Ψ hΨ => ⟨hΨ, fun f _ Φ hΦ hTΦ => funext fun X => ?_⟩⟩
  rw [(hT.2.1 F E σ d Φ hΦ).2.1 (R.ι w y) t u hM X, hTΦ, show (u⁻¹).1 = M'.toBlocks₂₂ from rfl]
  set Z := X * M'.toBlocks₂₂ᵀ - X
  have hZo (w') (h : w' ≠ w) : d.cw w' Z = 0 := by
    unfold SD_k.cw; rw [Matrix.map_sub _ (map_sub _), ← SD_k.cw, ← SD_k.cw, Krd.cw_mul_k, Krd.cw_transpose_k,
      (hO' w' h).2, transpose_one, Matrix.mul_one, sub_self]
  have hZf : finOne F • Z = 0 := by
    rw [smul_sub, ← Matrix.mul_smul, ← Matrix.transpose_smul, hF', Matrix.transpose_smul, transpose_one,
      Matrix.mul_smul, Matrix.mul_one, sub_self]
  have hloc : R.loc w (X * M'.toBlocks₂₂ᵀ) = Matrix.of (R.loc w X) * a := by
    simp only [RD_k.loc]; rw [Krd.cw_mul_k, Krd.cw_transpose_k, hD', ← Matrix.mul_assoc, mapStar_mulR]
    congr 1; ext _ _; simp only [Matrix.map_apply, Matrix.transpose_apply, conjTranspose_apply, star_star]
  simp only [RD_k.tens, id]
  rw [hloc, show X * M'.toBlocks₂₂ᵀ = X + Z by simp only [Z]; abel, hΨ X Z hZo hZf]; ring
theorem stepM (hT : TAll_k) (y : GR d.n) (a : d.Mnc) (ha : IsUnit a.det) (hy : mR y = mLoc a) :
    ∃ c : ℂ, c ≠ 0 ∧ R.StepOK w (R.ι w y) (fun f u => c * f (Matrix.of u * a)) id := by
  obtain ⟨t, -, -, -, hS⟩ := R.stepM_gen w hT y a ha hy
  exact ⟨_, mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2
    (Real.rpow_pos_of_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) (absE_ne _).symm) _).ne'), hS⟩
theorem stepN (hT : TAll_k) (y : GR d.n) (b : d.Mnc) (hb : bᴴ = b) (hy : mR y = nU b) :
    R.StepOK w (R.ι w y) (fun f u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * f u) id := by
  set M := inFrame d.b (R.ι w y)
  have hw : d.cw w M = nU (R.ζ • b) := by rw [R.cw_iota_pf w y, hy, dZ_conj_nU (Krd.zeta_ne R.hζ)]
  have ho := R.off_w w (y := y)
  have o1 := one_blocks (n := d.n) (1 : ℂ); simp only [one_smul] at o1
  have of := one_blocks (n := d.n) (finOne F • (1 : AE F E))
  have hf' : finOne F • M = (finOne F • (1 : AE F E)) • (1 : d.Mn2) := by rw [R.off_f w y, smul_one_smul]
  have hM : M = fromBlocks 1 M.toBlocks₁₂ 0 1 := by
    have e11 : M.toBlocks₁₁ = 1 := Place.cw_ext_k d (fun w' => by
        rw [Krd.cw_one_k]; show (d.cw w' M).toBlocks₁₁ = 1
        by_cases h : w' = w; · rw [h, hw]; simp [nU]
        · rw [ho w' h]; exact o1.1) (by show (finOne F • M).toBlocks₁₁ = _; rw [hf', of.1, smul_one_smul])
    have e21 : M.toBlocks₂₁ = 0 := Place.cw_ext_k d (fun w' => by
        unfold SD_k.cw; rw [Matrix.map_zero _ (map_zero _)]; show (d.cw w' M).toBlocks₂₁ = 0
        by_cases h : w' = w; · rw [h, hw]; simp [nU]
        · rw [ho w' h]; exact o1.2.2.1) (by show (finOne F • M).toBlocks₂₁ = _; rw [hf', of.2.2.1, smul_zero])
    have e22 : M.toBlocks₂₂ = 1 := Place.cw_ext_k d (fun w' => by
        rw [Krd.cw_one_k]; show (d.cw w' M).toBlocks₂₂ = 1
        by_cases h : w' = w; · rw [h, hw]; simp [nU]
        · rw [ho w' h]; exact o1.2.2.2) (by show (finOne F • M).toBlocks₂₂ = _; rw [hf', of.2.2.2, smul_one_smul])
    exact (Matrix.fromBlocks_toBlocks M).symm.trans (by rw [e11, e21, e22])
  have hβw : d.cw w M.toBlocks₁₂ = R.ζ • b := by show (d.cw w M).toBlocks₁₂ = _; rw [hw]; simp [nU]
  have hβo (w') (h : w' ≠ w) : d.cw w' M.toBlocks₁₂ = 0 := by
    show (d.cw w' M).toBlocks₁₂ = _; rw [ho w' h]; exact o1.2.1
  have hβf : finOne F • M.toBlocks₁₂ = 0 := by show (finOne F • M).toBlocks₁₂ = _; rw [hf', of.2.1]
  refine ⟨fun f ⟨φ, hφ⟩ => by
    subst hφ
    obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.CompanionTheory.QuadChirp.exists_schwartz_chirp_mul d.m d.n ((R.sg w : ℤ) : ℝ) b hb φ
    exact ⟨ψ, by rw [hψ]; funext _; push_cast; rfl⟩,
    fun Ψ hΨ => ⟨hΨ, fun f _ Φ hΦ hTΦ => funext fun X => by
      rw [(hT.2.1 F E σ d Φ hΦ).1 (R.ι w y) _ hM X, R.psi_nU w b hb _ hβw hβo hβf X, hTΦ]
      simp only [RD_k.tens, id]; ring⟩⟩
theorem stepW_exp (hT : TAll_k) (hA : SiegelWeilDatumProperties) (ε : ℤˣ) (w₀ : d.G) (hw : d.IsW ε w₀) :
    ∃ (C : ℂ) (B : d.MF → d.MF), C ≠ 0 ∧ R.StepOK w w₀ (fun f u => C * ∫ v : Fin d.m → Fin d.n → ℂ,
      Complex.exp (2 * Real.pi * Complex.I * (((-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) *
        Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * f v) B := by
  obtain ⟨⟨ν, hν⟩, -, -⟩ := hA F E σ d
  obtain ⟨C, μ', hC, -, hfact⟩ := KFock.intFact_k d R w ν hν
  have hs : (-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr (Units.ne_zero _)))
      (Int.cast_ne_zero.mpr (Units.ne_zero _))) (KW.zeta_ne_k R)
  refine ⟨(C : ℂ), fun Ψ X => ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ', by exact_mod_cast hC.ne',
    KW.locFT_sw _ _ hs, fun Ψ hΨ => ⟨fun X Z hZ1 hZ2 => integral_congr_ae <| .of_forall fun Z₀ => by
      dsimp only; rw [KW.psi_add_left_k, KW.gram_supp_cmp_k d w ⟨hZ1, hZ2⟩ Z₀.2, KW.psi_zero_gram_k, mul_one],
    fun f _ Φ hΦ hTΦ => funext fun X => ?_⟩⟩
  rw [hT.2.2.1 F E σ d ν hν ε w₀ hw Φ hΦ X, hTΦ]
  let Ψ' : d.MF := fun Z => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z - KW.insL_k R w (R.loc w Z)))) * Ψ Z
  have hΨ' : d.IsAwayW w Ψ' := fun X' Z hZ1 hZ2 => by
    simp only [Ψ']; rw [KW.rest_inv_k R w X' Z ⟨hZ1, hZ2⟩, hΨ X' Z hZ1 hZ2]
  have e : (fun Z => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * R.tens w f Ψ Z) =
      R.tens w (fun u => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (KW.insL_k R w u))) * f u) Ψ' := funext fun Z => by
    simp only [RD_k.tens, Ψ']
    have h := KW.psi_add_right_k d ε X (KW.insL_k R w (R.loc w Z)) (Z - KW.insL_k R w (R.loc w Z))
    rw [add_sub_cancel] at h; rw [h]; ring
  rw [e, hfact _ Ψ' hΨ', show ∫ Z, Ψ' Z.1 ∂μ' = ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z.1)) * Ψ Z.1 ∂μ' from
    integral_congr_ae (.of_forall fun Z => by
      simp only [Ψ']; rw [KFock.loc_of_mem_k d R w Z.2, KW.insL_zero_k, sub_zero])]
  simp only [RD_k.tens, KW.kernel_k R w ε X]
theorem stepW (hT : TAll_k) (hA : SiegelWeilDatumProperties) (ε : ℤˣ) (w₀ : d.G) (hw : d.IsW ε w₀) :
    ∃ (C s : ℂ) (B : d.MF → d.MF), s ≠ 0 ∧ R.StepOK w w₀ (fun f u => C * ∫ v : Fin d.m → Fin d.n → ℂ,
      Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * f v) B :=
  let ⟨C, B, _, hW⟩ := R.stepW_exp w hT hA ε w₀ hw
  ⟨C, _, B, div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Int.cast_ne_zero.mpr (Units.ne_zero _)))
    (Int.cast_ne_zero.mpr (Units.ne_zero _))) (KW.zeta_ne_k R), hW⟩
private theorem stepM_val (hT : TAll_k) (y : GR d.n) (a : d.Mnc) (ha : IsUnit a.det) (hy : mR y = mLoc a) :
    R.StepOK w (R.ι w y) (fun f u => (d.chiW w a.det * (‖a.det‖ : ℂ) ^ d.m) * f (Matrix.of u * a)) id := by
  obtain ⟨t, ht, ho, hf, hS⟩ := R.stepM_gen w hT y a ha hy
  have hc : (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) =
      d.chiW w a.det * (‖a.det‖ : ℂ) ^ d.m := by
    rw [chi_det (d := d) w t a ht ho hf, absE_det (d := d) w t a ht ho hf, ← Real.rpow_natCast ‖a.det‖ 2,
      ← Real.rpow_mul (norm_nonneg _), show ((2 : ℕ) : ℝ) * ((d.m : ℝ) / 2) = (d.m : ℝ) by push_cast; ring,
      Real.rpow_natCast]; push_cast; rfl
  simpa only [hc] using hS
end ExplicitW
section ImplicitW
variable {d : SD_k σ} (R : RD_k d) {w : InfinitePlace F} {L : GR d.n → d.LF → d.LF}
private theorem tens_cancel {Ψ : d.MF} (hΨ : d.IsAwayW w Ψ) (h0 : Ψ ≠ 0) {g g' : d.LF}
    (h : R.tens w g Ψ = R.tens w g' Ψ) : g = g' := by
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by by_contra hc; push Not at hc; exact h0 (funext hc)
  funext u; obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
  have := congrFun h (X₀ + Z); simp only [RD_k.tens, hZ3, hΨ X₀ Z hZ1 hZ2] at this
  exact mul_right_cancel₀ hX₀ this
private theorem exists_adm (hT : TAll_k) {Ψ : d.MF} (hΨ : R.GoodAway w Ψ) {f : d.LF} (hf : IsSw f) :
    ∃ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ := (hT.1 F E σ d).2.1 _ (hΨ.2.2 f hf)
theorem locOp_one (hT : TAll_k) (hG : GoodAwayEx_k) (hL : R.IsLocOp w L) (f : d.LF) (hf : IsSw f) : L 1 f = f := by
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w; obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e := (hL 1 f hf).2 Ψ hΨ.1 Φ hΦ hT'; rw [map_one, map_one, one_apply_eq_self, hT'] at e
  exact (R.tens_cancel hΨ.1 hΨ.2.1 e).symm
theorem locOp_mul (hT : TAll_k) (hG : GoodAwayEx_k) (hL : R.IsLocOp w L) (y y' : GR d.n) (f : d.LF) (hf : IsSw f) :
    L (y * y') f = L y (L y' f) := by
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w; obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e2 := (hL y (L y' f) (hL y' f hf).1).2 Ψ hΨ.1 _ (d.om_sch _ Φ hΦ) ((hL y' f hf).2 Ψ hΨ.1 Φ hΦ hT')
  have e3 := (hL (y * y') f hf).2 Ψ hΨ.1 Φ hΦ hT'; rw [map_mul, map_mul, mul_apply_eq_comp] at e3
  exact R.tens_cancel hΨ.1 hΨ.2.1 (e3.symm.trans e2)
theorem locOp_lin (hT : TAll_k) (hG : GoodAwayEx_k) (hL : R.IsLocOp w L) (y : GR d.n) (a : ℂ) (f g : d.LF)
    (hf : IsSw f) (hg : IsSw g) : L y (a • f + g) = a • L y f + L y g := by
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φf, hΦf, hTf⟩ := R.exists_adm hT hΨ hf; obtain ⟨Φg, hΦg, hTg⟩ := R.exists_adm hT hΨ hg
  have hTΦ : d.T (a • Φf + Φg) = R.tens w (a • f + g) Ψ := by
    rw [KFock.T_add_k, KFock.T_smul_k, hTf, hTg]; funext _
    simp only [RD_k.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have e := (hL y _ (isSw_lin a hf hg)).2 Ψ hΨ.1 _ (d.sch.add_mem (d.sch.smul_mem a hΦf) hΦg) hTΦ
  rw [map_add (f := _), map_smul, KFock.T_add_k, KFock.T_smul_k, (hL y f hf).2 Ψ hΨ.1 Φf hΦf hTf,
    (hL y g hg).2 Ψ hΨ.1 Φg hΦg hTg] at e
  refine R.tens_cancel hΨ.1 hΨ.2.1 (e.symm ▸ funext fun _ => ?_)
  simp only [RD_k.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
theorem locOp_nU (hT : TAll_k) (hG : GoodAwayEx_k) (hL : R.IsLocOp w L) (y : GR d.n) (b : d.Mnc)
    (hb : bᴴ = b) (hy : mR y = nU b) (f : d.LF) (hf : IsSw f) :
    L y f = fun u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * f u := by
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w; obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  exact R.tens_cancel hΨ.1 hΨ.2.1
    (((hL y f hf).2 Ψ hΨ.1 Φ hΦ hT').symm.trans (((R.stepN w hT y b hb hy).2 Ψ hΨ.1).2 f hf Φ hΦ hT'))
theorem locOp_mM (hT : TAll_k) (hG : GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∃ c : d.Mnc → ℂ, (∀ a, IsUnit a.det → c a ≠ 0) ∧
      ∀ (y : GR d.n) (a : d.Mnc), IsUnit a.det → mR y = mLoc a → ∀ f, IsSw f →
        L y f = fun u => c a * f (Matrix.of u * a) := by
  classical
  refine ⟨fun a => if h : IsUnit a.det ∧ ∃ y : GR d.n, mR y = mLoc a then
    (R.stepM w hT h.2.choose a h.1 h.2.choose_spec).choose else 1, fun a _ => ?_, fun y a ha hy f hf => ?_⟩
  · by_cases h : IsUnit a.det ∧ ∃ y : GR d.n, mR y = mLoc a
    · simp only [dite_eq_left h]; exact (R.stepM w hT h.2.choose a h.1 h.2.choose_spec).choose_spec.1
    · simp only [dite_eq_right h]; exact one_ne_zero
  · have h : IsUnit a.det ∧ ∃ y : GR d.n, mR y = mLoc a := ⟨ha, y, hy⟩
    have hy0 : h.2.choose = y := Subtype.ext (Units.ext (h.2.choose_spec.trans hy.symm))
    simp only [dite_eq_left h]; rw [← hy0]
    obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w; obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
    exact R.tens_cancel hΨ.1 hΨ.2.1 (((hL h.2.choose f hf).2 Ψ hΨ.1 Φ hΦ hT').symm.trans
      (((R.stepM w hT h.2.choose a h.1 h.2.choose_spec).choose_spec.2.2 Ψ hΨ.1).2 f hf Φ hΦ hT'))
theorem locOp_mM_law (w : InfinitePlace F) (hT : TAll_k) (hG : GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∃ k : ℤ, ∀ (y : GR d.n) (a : d.Mnc), IsUnit a.det → mR y = mLoc a → ∀ f, IsSw f →
      L y f = fun u => (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ d.m * f (Matrix.of u * a) := by
  obtain ⟨k, hk⟩ := d.chiW_form w; refine ⟨k, fun y a ha hy f hf => ?_⟩
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w; obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  rw [R.tens_cancel hΨ.1 hΨ.2.1 (((hL y f hf).2 Ψ hΨ.1 Φ hΦ hT').symm.trans
    (((R.stepM_val w hT y a ha hy).2 Ψ hΨ.1).2 f hf Φ hΦ hT')), hk _ ha.ne_zero]; rfl
private theorem locOp_zero (hT : TAll_k) (hG : GoodAwayEx_k) (hL : R.IsLocOp w L) (y : GR d.n) : L y 0 = 0 := by
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w; have h0 : IsSw (0 : d.LF) := ⟨0, by ext; simp⟩
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ h0
  have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hT']; funext _; simp [RD_k.tens])
  have e := (hL y 0 h0).2 Ψ hΨ.1 Φ hΦ hT'; rw [hΦ0, map_zero, d.T_zero] at e
  exact R.tens_cancel hΨ.1 hΨ.2.1 (e.symm ▸ funext fun _ => by simp [RD_k.tens])
private theorem locOp_nbar_of (hT : TAll_k) (hG : GoodAwayEx_k) (hL : R.IsLocOp w L) {ε : ℤˣ} {w₀ : d.G}
    (hw₀ : d.IsW ε w₀) {C s : ℂ} {B : d.MF → d.MF} (hW' : R.StepOK w w₀ (locFT C s) B) :
    ∃ κ : ℂ, κ ≠ 0 ∧ (∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f) ∧
      (∀ (y : GR d.n) (c : d.Mnc), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f))))) ∧
      ∀ (y : GR d.n) (c : d.Mnc), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        locFT C s (L y f) = chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f) := by
  have hsch := d.om_sch
  have h4 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hW'
  rw [w_four hw₀] at h4
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by by_contra hc; push Not at hc; exact hΨ.2.1 (funext hc)
  have hB4 : d.IsAwayW w (B (B (B (B Ψ)))) := (h4.2 Ψ hΨ.1).1
  have key (f : d.LF) (hf : IsSw f) (X) : f (R.loc w X) * Ψ X =
      locFT C s (locFT C s (locFT C s (locFT C s f))) (R.loc w X) * B (B (B (B Ψ))) X := by
    obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
    have e := (h4.2 Ψ hΨ.1).2 f hf Φ hΦ hT'; rw [map_one, one_apply_eq_self, hT'] at e; exact congrFun e X
  have key0 (f : d.LF) (hf : IsSw f) (u) : f u * Ψ X₀ =
      locFT C s (locFT C s (locFT C s (locFT C s f))) u * B (B (B (B Ψ))) X₀ := by
    obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
    have := key f hf (X₀ + Z); rwa [hZ3, hΨ.1 X₀ Z hZ1 hZ2, hB4 X₀ Z hZ1 hZ2] at this
  by_cases hb : B (B (B (B Ψ))) X₀ = 0
  · have hz (f : d.LF) (hf : IsSw f) : f = 0 := funext fun u =>
      (mul_eq_zero.mp (by simpa [hb] using key0 f hf u)).resolve_right hX₀
    exact ⟨1, one_ne_zero, fun f hf => by rw [hz f hf]; simp [locFT_zero],
      fun y _ _ _ f hf => by rw [hz f hf, R.locOp_zero hT hG hL y]; simp [locFT_zero, chirp_zero],
      fun y _ _ _ f hf => by rw [hz f hf, R.locOp_zero hT hG hL y]; simp [locFT_zero, chirp_zero]⟩
  · set κ := Ψ X₀ / B (B (B (B Ψ))) X₀; have hκ0 : κ ≠ 0 := div_ne_zero hX₀ hb
    have h4f (f : d.LF) (hf : IsSw f) : locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f := funext fun u => by
      have := key0 f hf u; simp only [Pi.smul_apply, smul_eq_mul, κ]; field_simp; linear_combination -this
    have hmain (y : GR d.n) (c : d.Mnc) (hc : cᴴ = c) (hy : mR y = nbLoc c) (f) (hf : IsSw f) :
        IsSw (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)))) := by
      obtain ⟨y', hy', hrel⟩ := R.oppositeUnipotent_weylConj w hw₀ y c hc hy
      have hx : ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)ᴴ = (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c := by
        rw [conjTranspose_smul, hc, show star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ by
          rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp [Complex.inv_I]]
      have hN : R.StepOK w (R.ι w y') (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)) id :=
        R.stepN w hT y' _ hx hy'
      refine ⟨hN.1 _ (hW'.1 f hf), ?_⟩
      by_cases hf0 : ∀ u, f u = 0
      · rw [show f = 0 from funext hf0, R.locOp_zero hT hG hL y]; simp [locFT_zero, chirp_zero]
      push Not at hf0; obtain ⟨u₀, hu₀⟩ := hf0
      have hBΨ (X) : B (B (B (B Ψ))) X = κ⁻¹ * Ψ X := by
        obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u₀; have := key f hf (X + Z)
        rw [hZ3, hΨ.1 X Z hZ1 hZ2, hB4 X Z hZ1 hZ2, h4f f hf] at this
        simp only [Pi.smul_apply, smul_eq_mul] at this
        rw [eq_inv_mul_iff_mul_eq₀ hκ0]; exact mul_left_cancel₀ hu₀ (by linear_combination -this)
      have hc3 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hN) hW'
      obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
      have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'; rw [hrel] at e1
      refine R.tens_cancel hΨ.1 hΨ.2.1 (e1.symm.trans (((hc3.2 Ψ hΨ.1).2 f hf Φ hΦ hT').trans (funext fun _ => ?_)))
      simp only [RD_k.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hBΨ]; ring
    refine ⟨κ, hκ0, h4f, fun y c hc hy f hf => (hmain y c hc hy f hf).2, fun y c hc hy f hf => ?_⟩
    obtain ⟨hsw, heq⟩ := hmain y c hc hy f hf
    rw [heq, locFT_smul, h4f _ hsw, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
theorem locOp_nbar (hT : TAll_k) (hA : SiegelWeilDatumProperties) (hG : GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∃ (C s κ : ℂ) (ε : ℤˣ), s ≠ 0 ∧ κ ≠ 0 ∧
      (∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f) ∧
      (∀ (y : GR d.n) (c : d.Mnc), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f))))) ∧
      (∀ (y : GR d.n) (c : d.Mnc), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        locFT C s (L y f) = chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧
      ‖s‖ = 2 ∧ ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ = -1 := by
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d; obtain ⟨C, B, -, hW⟩ := R.stepW_exp w hT hA ε w₀ hw₀
  set s : ℂ := -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ
  have hζn : ‖R.ζ‖ = 1 := by rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp
  have hu (u : ℤˣ) : ‖((u : ℤ) : ℂ)‖ = 1 := by rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> simp
  have hsn : ‖s‖ = 2 := by rw [norm_div, norm_mul, norm_mul, hu, hu, hζn]; norm_num
  have hη : ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ = -1 := by
    rw [R.isW_eps w hw₀]; rcases R.hζ with ⟨he, hz⟩ | ⟨he, hz⟩ <;> rw [he, hz] <;> simp [Complex.inv_I]
  obtain ⟨κ, hκ0, h4, hnb, hft⟩ := R.locOp_nbar_of hT hG hL hw₀ hW
  exact ⟨C, s, κ, ε, fun h0 => by rw [h0, norm_zero] at hsn; norm_num at hsn, hκ0, h4, hnb, hft, hsn, hη⟩
theorem localOperator_longWeyl_integral (hT : TAll_k) (hA : SiegelWeilDatumProperties) (hG : GoodAwayEx_k)
    (hL : R.IsLocOp w L) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ y : GR d.n, mR y = JJ d.n → ∀ f, IsSw f → L y f 0 = C * ∫ v, f v := by
  obtain ⟨C₀, s, κ, ε, -, hκ, h4, hnb, -, hs2, hη⟩ := R.locOp_nbar hT hA hG hL
  have hC₀ : C₀ ≠ 0 := fun h0 => hκ <| by
    have h := congrFun (h4 _ (KFock.isSw_fP 1)) 0
    simp only [locFT, h0, zero_mul, Pi.smul_apply, smul_eq_mul, fP, evX, gs, map_one, one_mul,
      Pi.zero_apply, norm_zero, sq, mul_zero, Finset.sum_const_zero, neg_zero, Complex.ofReal_zero,
      Complex.exp_zero, mul_one] at h; exact h.symm
  have hsn : ‖s‖ = 2 * |((R.sg w : ℤ) : ℝ)| := by
    rw [hs2, show |((R.sg w : ℤ) : ℝ)| = 1 from by rcases Int.units_eq_one_or (R.sg w) with h | h <;> rw [h] <;> simp,
      mul_one]
  obtain ⟨c, hc, hfres⟩ := _root_.GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero d.m d.n C₀ s ((R.sg w : ℤ) : ℝ)
    hC₀ (Int.cast_ne_zero.mpr (Units.ne_zero _)) hsn
  refine ⟨κ⁻¹ * c, mul_ne_zero (inv_ne_zero hκ) hc, fun y hy f hf => ?_⟩
  obtain ⟨y₁, y₂, h1, h2, rfl⟩ := jj_split y hy; have hf1 := (hL y₁ f hf).1; have hf2 := (hL y₂ _ hf1).1
  rw [R.locOp_mul hT hG hL (y₁ * y₂) y₁ f hf, R.locOp_mul hT hG hL y₁ y₂ _ hf1,
    R.locOp_nU hT hG hL y₁ 1 conjTranspose_one h1 _ hf2,
    hnb y₂ (-1) (by rw [Matrix.conjTranspose_neg, conjTranspose_one]) h2 _ hf1,
    R.locOp_nU hT hG hL y₁ 1 conjTranspose_one h1 f hf,
    show (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • (-1 : d.Mnc) = 1 from by rw [hη, neg_smul, one_smul, neg_neg]]
  obtain ⟨φ, hφ⟩ := hf
  have hch (g : d.LF) : chirp ((R.sg w : ℤ) : ℂ) (1 : d.Mnc) g = fun u => Complex.exp (2 * Real.pi * Complex.I *
      (((R.sg w : ℤ) : ℝ) : ℂ) * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u :=
    funext fun _ => by simp only [chirp, Matrix.one_mul]; push_cast; rfl
  change Complex.exp _ * (κ⁻¹ • locFT C₀ s (locFT C₀ s (locFT C₀ s (chirp _ 1 (locFT C₀ s (chirp _ 1 f)))))) 0 = _
  rw [show Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace ((1 : d.Mnc) * ((Matrix.of (0 : Fin d.m → Fin d.n → ℂ))ᴴ *
        Matrix.of (0 : Fin d.m → Fin d.n → ℂ)))) = 1
    by simp only [Matrix.of_zero, Matrix.conjTranspose_zero, Matrix.mul_zero, trace_zero, mul_zero, Complex.exp_zero],
    one_mul, Pi.smul_apply, smul_eq_mul, hch, hch, ← hφ]
  have := hfres φ; simp only [locFT] at this ⊢; rw [this, hφ]; ring
end ImplicitW
end RD_k
namespace KLI
theorem locOp_cont_k (hT : TAll_k) {d : SD_k σ} (R : RD_k d) {w : InfinitePlace F} {L : GR d.n → d.LF → d.LF}
    (hL : R.IsLocOp w L) (P : PX d.m d.n) (u : Fin d.m → Fin d.n → ℂ) : Continuous fun y => L y (fP P) u := by
  obtain ⟨Ψ, hΨ, hΨ0⟩ := KFock.goodAway0_k R w; obtain ⟨Φ, hΦ, hTΦ⟩ := R.exists_adm hT hΨ (KFock.isSw_fP P)
  obtain ⟨Z, hZw, hZf, hZu⟩ := R.loc_surj w 0 u
  have hΨZ : Ψ Z = Ψ 0 := by simpa only [zero_add] using hΨ.1 0 Z hZw hZf
  have hZu' : R.loc w Z = u := by simpa only [zero_add] using hZu
  have key (y) : L y (fP P) u = d.T (d.om (R.ι w y) Φ) Z / Ψ 0 := by
    have e := congrFun ((hL y (fP P) (KFock.isSw_fP P)).2 Ψ hΨ.1 Φ hΦ hTΦ) Z
    rw [e]; simp only [RD_k.tens, hZu', hΨZ]; field_simp
  set v := Z * (incM F d.b.1.toCols₂)ᵀ
  have hev : finOne F • d.dd.e v = 0 := by
    rw [← LinearEquiv.map_smul, show finOne F • v = 0 by rw [← Matrix.smul_mul, hZf, Matrix.zero_mul], map_zero]
  have hv (i) : ((d.dd.e v).1 i).2 = 0 ∧ ((d.dd.e v).2 i).2 = 0 := by
    have e1 := congrFun (congrArg Prod.fst hev) i; have e2 := congrFun (congrArg Prod.snd hev) i
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply] at e1 e2
    exact ⟨by simpa [show (finOne F).2 = 1 from rfl] using congrArg Prod.snd e1,
           by simpa [show (finOne F).2 = 1 from rfl] using congrArg Prod.snd e2⟩
  exact (((d.ok.dbl.weil.2.1.cont _ (rho_adm F d.B.ψ d.ok.good.std d.ok.dbl.adm (d.dd.e v) hv) Φ hΦ).comp
    (R.cont w)).div_const (Ψ 0)).congr fun y => (key y).symm
theorem locHyp_of_k (hT : TAll_k) (hA : SiegelWeilDatumProperties) {d : SD_k σ} (R : RD_k d) {w : InfinitePlace F}
    {L : GR d.n → d.LF → d.LF} (hL : R.IsLocOp w L) : LocHyp (R.sg w) L := by
  have hG := KFock.goodAwayEx_k; obtain ⟨k, hk⟩ := R.locOp_mM_law w hT hG hL
  obtain ⟨C, s, κ, ε, hs, hκ, h4, hf, -, hs2, hη⟩ := R.locOp_nbar hT hA hG hL
  exact ⟨fun y f hf => (hL y f hf).1, R.locOp_one hT hG hL, R.locOp_mul hT hG hL, R.locOp_lin hT hG hL,
    R.locOp_nU hT hG hL, ⟨k, hk⟩, ⟨C, s, κ, ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹, hs, hκ, hs2, hη, h4, hf⟩,
    R.localOperator_longWeyl_integral hT hA hG hL, locOp_cont_k hT R hL⟩
theorem locInst_of_k (hT : TAll_k) (hA : SiegelWeilDatumProperties) (_hF : FockMem_k) (_hLi : LiftEx_k) : LocInst_k :=
  fun _ _ _ _ _ _ _ _ d R w _ hL =>
    let ⟨sL, ρ, e, hD, h1, h2⟩ := locData_of (locHyp_of_k hT hA R hL)
    ⟨sL, ρ, pOf (R.sg w) d.m, qOf (R.sg w) d.m, e, fun hnm => goodSig_pq _ hnm, hD, h1, h2⟩
end KLI
def SD_k.Indep (d : SD_k σ) (w : InfinitePlace F) (Ψ : d.MF) : Prop :=
  ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X
def AwayAct_k : Prop := ForAllSD fun {_ _ _ _ _ _ _ _} d => ∀ (R : RD_k d) w (x : d.G), d.cw w (inFrame d.b x) = 1 →
  ∃ A : d.MF → d.MF, ∀ Ψ, d.Indep w Ψ → d.Indep w (A Ψ) ∧
    ∀ f, IsSw f → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om x Φ) = R.tens w f (A Ψ)
def FinAct_k : Prop := ForAllSD fun {_ _ _ _ _ _ _ _} d => ∀ x : d.G, (∀ w, d.cw w (inFrame d.b x) = 1) →
  ∀ g ∈ SB d.Af3, ∃ g' ∈ SB d.Af3, ∀ f : d.MF, (∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X) →
    ∀ Φ ∈ d.sch, d.T Φ = (fun X => f X * g fun k => (d.crd X k).2) →
      d.T (d.om x Φ) = fun X => f X * g' fun k => (d.crd X k).2
namespace KAway
theorem inFrame_mul_k (d : SD_k σ) (x y : d.G) :
    inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := d.inFrame_mul x y
theorem inFrame_one_k (d : SD_k σ) : inFrame d.b (1 : d.G) = 1 := d.inFrame_one
theorem inFrame_inj_k (d : SD_k σ) {x y : d.G} (h : inFrame d.b x = inFrame d.b y) : x = y := d.inFrame_inj h
namespace W
private theorem cw_eW_self (d : SD_k σ) (w : InfinitePlace F) {p q : Type} (M : Matrix p q (AE F E)) :
    d.cw w (eW w • M) = d.cw w M := Matrix.ext fun _ _ => by simp [SD_k.cw, piInf_eW]
private theorem cw_eW_ne (d : SD_k σ) {w w' : InfinitePlace F} (h : w' ≠ w) {p q : Type} (M : Matrix p q (AE F E)) :
    d.cw w' (eW w • M) = 0 := Matrix.ext fun _ _ => by simp [SD_k.cw, piInf_eW, h]
private theorem eW_smul_eq_iff (d : SD_k σ) (w : InfinitePlace F) {p q : Type} (M M' : Matrix p q (AE F E)) :
    eW w • M = eW w • M' ↔ d.cw w M = d.cw w M' :=
  ⟨fun h => by rw [← cw_eW_self d w M, h, cw_eW_self], fun h => Place.cw_ext_k d (fun w' => by
    by_cases hw : w' = w; · subst hw; rw [cw_eW_self, cw_eW_self, h]
    · rw [cw_eW_ne d hw, cw_eW_ne d hw]) (by rw [finOne_eW_smul, finOne_eW_smul])⟩
private theorem gram_smul_l (d : SD_k σ) (a : AF F) (X Z : d.MxE) : d.gram (a • X) Z = a • d.gram X Z := by
  simp only [SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul]
private theorem gram_smul_r (d : SD_k σ) (a : AF F) (X Z : d.MxE) : d.gram X (a • Z) = a • d.gram X Z := by
  simp only [SD_k.gram, show (a • Z).map (cA σ) = a • Z.map (cA σ) from by ext _ _; simp [map_smul], Matrix.mul_smul]
private theorem gram_add_l (d : SD_k σ) (X X' Z : d.MxE) : d.gram (X + X') Z = d.gram X Z + d.gram X' Z := by
  simp only [SD_k.gram, Matrix.transpose_add, Matrix.add_mul]
private theorem gram_add_r (d : SD_k σ) (X Z Z' : d.MxE) : d.gram X (Z + Z') = d.gram X Z + d.gram X Z' := by
  simp only [SD_k.gram]; rw [Matrix.map_add _ (map_add _), Matrix.mul_add]
private theorem cw_eInf (d : SD_k σ) (w : InfinitePlace F) {p q : Type} (Z : Matrix p q (AE F E)) :
    d.cw w (eInf F • Z) = d.cw w Z := Matrix.ext fun _ _ => by
  simp only [SD_k.cw, Matrix.map_apply, Matrix.smul_apply, St.piInf_smul, eInf_fst_apply, map_one, one_mul]
private theorem cw_finOne (d : SD_k σ) (w : InfinitePlace F) {p q : Type} (Z : Matrix p q (AE F E)) :
    d.cw w (finOne F • Z) = 0 := Matrix.ext fun _ _ => by
  simp only [SD_k.cw, Matrix.map_apply, Matrix.smul_apply, Place.piInf_finOne, Matrix.zero_apply]
private theorem cw_zero_iff (d : SD_k σ) {p q : Type} (Z : Matrix p q (AE F E)) :
    (∀ w, d.cw w Z = 0) ↔ eInf F • Z = 0 :=
  ⟨fun h => Place.cw_ext_k d (fun w => by rw [cw_eInf, h w]; ext _ _; simp [SD_k.cw])
    (by rw [smul_smul, finOne_mul_eInf, zero_smul, smul_zero]),
   fun h w => by rw [← cw_eInf d w Z, h]; ext _ _; simp [SD_k.cw]⟩
private theorem crd_smul (d : SD_k σ) (c : AF F) (X : d.MxE) (k) : d.crd (c • X) k = c * d.crd X k := by
  simp only [SD_k.crd, Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
private theorem conj_split (d : SD_k σ) (hT : TAll_k) {α : Type*} (π : d.MxE → α) {g : d.G} {f : α → ℂ} {G : d.MF}
    {A₁ A₂ : (α → ℂ) → α → ℂ} {B₁ B₂ B' : d.MF → d.MF} {Φ : d.Fn} (hΦ : Φ ∈ d.sch)
    (hTΦ : d.T Φ = fun X => f (π X) * G X) (e : d.T (d.om g Φ) = fun X => A₁ (A₂ f) (π X) * B₁ (B' (B₂ G)) X)
    (key : ∀ u X, f u * G X = A₁ (A₂ f) u * B₁ (B₂ G) X) :
    d.T (d.om g Φ) = fun X => f (π X) * (if h : ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 then
      (G h.choose / B₁ (B₂ G) h.choose) • B₁ (B' (B₂ G)) else 0) X := by
  by_cases hz : (∀ u, f u = 0) ∨ ∀ X, G X = 0
  · have hΦ0 : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hTΦ]; funext X; rcases hz with hz | hz <;> simp [hz])
    subst hΦ0; rw [map_zero, d.T_zero]; funext X
    rcases hz with hz | hz; · simp [hz]
    · simp [dite_eq_right (show ¬ ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 from fun ⟨X₀, h, _⟩ => h (hz X₀))]
  · push Not at hz; obtain ⟨⟨u₀, hu₀⟩, ⟨X₁, hX₁⟩⟩ := hz
    have hex : ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 := ⟨X₁, hX₁, fun h0 => by
      have := key u₀ X₁; rw [h0, mul_zero] at this; exact mul_ne_zero hu₀ hX₁ this⟩
    have hA (u) : A₁ (A₂ f) u = f u * (G hex.choose / B₁ (B₂ G) hex.choose) := by
      have := key u hex.choose; rw [mul_div_assoc', eq_div_iff hex.choose_spec.2]; linear_combination -this
    rw [e]; funext X; simp only [dite_eq_left hex, Pi.smul_apply, smul_eq_mul, hA]; ring
private theorem inFrame_inv_of (d : SD_k σ) (x : d.G) (N : d.Mn2) (h : inFrame d.b x * N = 1) :
    inFrame d.b x⁻¹ = N :=
  left_inv_eq_right_inv (GlobalTheory.EisBL.DoubledParabolic.inFrame_inv_mul d.b x) h
private theorem exists_of_inU {d : SD_k σ} {ε : ℤˣ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (M : d.Mn2)
    (hM : Mᵀ * jF d.n ε * M.map (cA σ) = jF d.n ε) : ∃ x : d.G, inFrame d.b x = M := by
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
  have hJJ : (jF d.n ε : d.Mn2) * (((ε : ℤ) : AE F E) • jF d.n ε) = 1 := by
    rw [Matrix.mul_smul, jF, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul]
    congr 1 <;> simp [smul_smul, hεε]
  have hu := Matrix.isUnit_det_of_right_inverse
    (show Mᵀ * (jF d.n ε * M.map (cA σ) * (((ε : ℤ) : AE F E) • jF d.n ε)) = 1
    by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hM, hJJ])
  rw [Matrix.det_transpose] at hu
  exact kunf.exists_of_frame hε M M⁻¹ (Matrix.mul_nonsing_inv M hu) hM
private theorem adDecomp (d : SD_k σ) (ε : ℤˣ) (w : d.G) (hw : d.IsW ε w) (e : AF F) (he : e * e = e) (x : d.G)
    (hx : e • inFrame d.b x = e • (1 : d.Mn2)) :
    ∃ (x₁ x₂ x₃ x₄ : d.G) (t c b : d.Mn) (a a' : d.Gn), x = x₁ * (w * x₂ * w⁻¹) * x₃ * x₄ ∧
      inFrame d.b x₁ = fromBlocks 1 t 0 1 ∧ inFrame d.b x₂ = fromBlocks 1 c 0 1 ∧
      inFrame d.b x₃ = fromBlocks a.1 0 0 a'.1 ∧ inFrame d.b x₄ = fromBlocks 1 b 0 1 ∧
      e • t = 0 ∧ e • c = 0 ∧ e • b = 0 ∧ e • a.1 = e • (1 : d.Mn) ∧ e • a'.1 = e • (1 : d.Mn) := by
  open Matrix in
  obtain ⟨ε₀, hε₀⟩ := d.ok.frame.1; set X := inFrame d.b x with hXdef
  set A := X.toBlocks₁₁; set B := X.toBlocks₁₂; set C := X.toBlocks₂₁; set D := X.toBlocks₂₂
  have hXb : X = fromBlocks A B C D := (fromBlocks_toBlocks X).symm
  have h1 : ∀ y : d.G, IsUnit (inFrame d.b y).det :=
    fun y => Matrix.isUnit_det_of_left_inverse (GlobalTheory.EisBL.DoubledParabolic.inFrame_inv_mul d.b y)
  have heA : e • A = e • (1 : d.Mn) := by rw [← smul_toBlocks₁₁, hx, smul_toBlocks₁₁, one_toBlocks₁₁]
  have heB : e • B = 0 := by rw [← smul_toBlocks₁₂, hx, smul_toBlocks₁₂, one_toBlocks₁₂, smul_zero]
  have heC : e • C = 0 := by rw [← smul_toBlocks₂₁, hx, smul_toBlocks₂₁, one_toBlocks₂₁, smul_zero]
  have heD : e • D = e • (1 : d.Mn) := by rw [← smul_toBlocks₂₂, hx, smul_toBlocks₂₂, one_toBlocks₂₂]
  obtain ⟨t, ht, het, hunit⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator d.cm (ε₀ : ℤ) (Int.units_coe_mul_self ε₀) X (h1 x) e he heA
  have hni (u : d.Mn) {y : d.G} (hy : inFrame d.b y = nM u) : inFrame d.b y⁻¹ = nM (-u) :=
    inFrame_inv_of d y _ (by rw [hy, nM, nM, fromBlocks_multiply]; simp [fromBlocks_one])
  obtain ⟨x₁, hx₁⟩ := exists_of_inU hε₀ (nM t) ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) t).2 ht)
  set A' := A - t * C; set B' := B - t * D
  have hY : inFrame d.b (x₁⁻¹ * x) = fromBlocks A' B' C D := by
    rw [d.inFrame_mul, hni t hx₁, ← hXdef, hXb, nM, fromBlocks_multiply]; simp [A', B', sub_eq_add_neg]
  have h11 := upper_block_rank_one_update (cA σ).toRingHom (ε₀ : ℤ) _ (kunf.frame_eq hε₀ (x₁⁻¹ * x))
  rw [hY, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁] at h11
  set c₀ := C * A'⁻¹; set c := ((ε : ℤ) : AE F E) • c₀
  obtain ⟨x₂, hx₂⟩ := exists_of_inU hε₀ (nM c)
    ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) c).2 (cond_c (cA σ).toRingHom (ε₀ : ℤ) A' C hunit (Int.units_coe_mul_self ε₀) h11 (ε : ℤ)))
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by rw [← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one]
  have hwi : inFrame d.b w⁻¹ = fromBlocks 0 (((ε : ℤ) : AE F E) • 1) 1 0 :=
    inFrame_inv_of d w _ (by rw [hw, fromBlocks_multiply]; simp [smul_smul, hεε, fromBlocks_one])
  have hL : inFrame d.b (w * x₂ * w⁻¹) = fromBlocks 1 0 c₀ 1 := by
    rw [d.inFrame_mul, d.inFrame_mul, hw, hx₂, hwi, nM, fromBlocks_multiply, fromBlocks_multiply]
    simp [c, smul_smul, hεε]
  have hLi : inFrame d.b (w * x₂ * w⁻¹)⁻¹ = fromBlocks 1 0 (-c₀) 1 :=
    inFrame_inv_of d _ _ (by rw [hL, fromBlocks_multiply]; simp [fromBlocks_one])
  have hcA : c₀ * A' = C := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
  have hZ : inFrame d.b ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x)) = fromBlocks A' B' 0 (D - c₀ * B') := by
    rw [d.inFrame_mul, hLi, hY, fromBlocks_multiply]; simp [hcA, sub_eq_add_neg, add_comm]
  obtain ⟨hz1, hz2⟩ := blkUpper (cA σ).toRingHom (ε₀ : ℤ) A' B' (D - c₀ * B') (by rw [← hZ]; exact kunf.frame_eq hε₀ _)
  obtain ⟨x₄, hx₄⟩ := exists_of_inU hε₀ (nM (A'⁻¹ * B'))
    ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) _).2 (cond_b (cA σ).toRingHom (ε₀ : ℤ) (_root_.GlobalTheory.ThK.Dbl.cA_cA d.cm)
      A' B' (D - c₀ * B') hunit hz1 hz2))
  have hx₃ : inFrame d.b ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹) = fromBlocks A' 0 0 (D - c₀ * B') := by
    rw [d.inFrame_mul, hZ, hni _ hx₄, nM, fromBlocks_multiply]; simp [Matrix.mul_nonsing_inv_cancel_left _ _ hunit]
  have hdet := h1 ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹); rw [hx₃, det_fromBlocks_zero₁₂] at hdet
  have heB' : e • B' = 0 := by rw [smul_sub, ← Matrix.smul_mul, het, Matrix.zero_mul, heB, sub_zero]
  refine ⟨x₁, x₂, (w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹, x₄, t, c, A'⁻¹ * B', nonsingInvUnit A' hunit,
    nonsingInvUnit (D - c₀ * B') (isUnit_of_mul_isUnit_right hdet),
    by simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one],
    hx₁, hx₂, hx₃, hx₄, het,
    by rw [smul_comm, ← Matrix.smul_mul, heC, Matrix.zero_mul, smul_zero],
    by rw [← Matrix.mul_smul, heB', Matrix.mul_zero],
    by change e • (A - t * C) = _; rw [smul_sub, ← Matrix.smul_mul, het, Matrix.zero_mul, sub_zero, heA],
    by change e • (D - c₀ * B') = _; rw [smul_sub, ← Matrix.mul_smul, heB', Matrix.mul_zero, sub_zero, heD]⟩
section AwayStep
variable {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F)
private theorem stepN (hT : TAll_k) (x : d.G) (β : d.Mn) (hx : inFrame d.b x = fromBlocks 1 β 0 1) (hβ : eW w • β = 0) :
    R.StepOK w x id (fun Ψ X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * Ψ X) := by
  refine ⟨fun _ hf => hf, fun Ψ hΨ => ⟨fun X Z hZ hf => ?_, fun f _ Φ hΦ hTΦ => ?_⟩⟩
  · have hZe : eW w • Z = Z := Place.cw_ext_k d (fun w' => by
      by_cases hw : w' = w; · subst hw; rw [cw_eW_self]
      · rw [cw_eW_ne d hw, hZ w' hw]) (by rw [finOne_eW_smul, hf])
    have key : β * d.gram (X + Z) (X + Z) = β * d.gram X X := by
      rw [show d.gram (X + Z) (X + Z) = d.gram X X + (d.gram X Z + d.gram Z X + d.gram Z Z) by
            rw [gram_add_l, gram_add_r, gram_add_r]; abel,
        show d.gram X Z = eW w • d.gram X Z by rw [← gram_smul_r, hZe],
        show d.gram Z X = eW w • d.gram Z X by rw [← gram_smul_l, hZe],
        show d.gram Z Z = eW w • d.gram Z Z by rw [← gram_smul_l, hZe],
        ← smul_add, ← smul_add, Matrix.mul_add, Matrix.mul_smul, ← Matrix.smul_mul, hβ, Matrix.zero_mul, add_zero]
    simp only [key, hΨ X Z hZ hf]
  · funext X; rw [(hT.2.1 F E σ d Φ hΦ).1 x β hx X, hTΦ]; simp only [RD_k.tens, id]; ring
private theorem stepM (hT : TAll_k) (x : d.G) (a a' : d.Gn) (hx : inFrame d.b x = fromBlocks a.1 0 0 a'.1)
    (ha : eW w • a'.1 = eW w • (1 : d.Mn)) :
    R.StepOK w x id (fun Ψ X => (d.χ a.det : ℂ) * (((absE F E a.det : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) *
      Ψ (X * (a'⁻¹).1ᵀ)) := by
  have hc : d.cw w (a'⁻¹).1 = 1 := by
    have h2 : d.cw w ((a'⁻¹).1 * a'.1) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Krd.cw_one_k]
    rwa [Krd.cw_mul_k, (eW_smul_eq_iff d w a'.1 1).1 ha, Krd.cw_one_k, Matrix.mul_one] at h2
  refine ⟨fun _ hf => hf, fun Ψ hΨ => ⟨fun X Z hZ hf => ?_, fun f _ Φ hΦ hTΦ => ?_⟩⟩
  · simp only
    rw [Matrix.add_mul, hΨ (X * (a'⁻¹).1ᵀ) (Z * (a'⁻¹).1ᵀ)
      (fun w' hw' => by rw [Krd.cw_mul_k, hZ w' hw', Matrix.zero_mul]) (by rw [← Matrix.smul_mul, hf, Matrix.zero_mul])]
  · funext X; rw [(hT.2.1 F E σ d Φ hΦ).2.1 x a a' hx X, hTΦ]
    have hl : R.loc w (X * (a'⁻¹).1ᵀ) = R.loc w X := by
      unfold RD_k.loc; rw [Krd.cw_mul_k, Krd.cw_transpose_k, hc, transpose_one, Matrix.mul_one]
    simp only [RD_k.tens, id, hl]; ring
private theorem away_conj (hT : TAll_k) {x₁ x₂ x' : d.G} {A₁ A₂ : d.LF → d.LF} {B₁ B₂ B' : d.MF → d.MF}
    (h₁ : R.StepOK w x₁ A₁ B₁) (h₂ : R.StepOK w x₂ A₂ B₂) (h' : R.StepOK w x' id B') (h1 : x₁ * x₂ = 1) :
    ∃ B, R.StepOK w (x₁ * x' * x₂) id B := by
  have hc := R.step_comp w d.om_sch (R.step_comp w d.om_sch h₁ h') h₂; have h0 := R.step_comp w d.om_sch h₁ h₂
  refine ⟨fun Ψ => if h : ∃ X₀, Ψ X₀ ≠ 0 ∧ B₁ (B₂ Ψ) X₀ ≠ 0 then
      (Ψ h.choose / B₁ (B₂ Ψ) h.choose) • B₁ (B' (B₂ Ψ)) else 0,
    fun _ hf => hf, fun Ψ hΨ => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · dsimp only; split_ifs with h
    · exact fun X Z hZ hfz => by simp only [Pi.smul_apply]; congr 1; exact (hc.2 Ψ hΨ).1 X Z hZ hfz
    · exact fun _ _ _ _ => rfl
  · have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ; rw [h1, map_one, one_apply_eq_self, hTΦ] at e0
    exact conj_split d hT (R.loc w) hΦ hTΦ ((hc.2 Ψ hΨ).2 f hf Φ hΦ hTΦ) fun u X => by
      obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u; have := congrFun e0 (X + Z)
      simp only [RD_k.tens, hZ3, hΨ X Z hZ1 hZ2, (h0.2 Ψ hΨ).1 X Z hZ1 hZ2] at this; exact this
end AwayStep
section FinStep
variable (d : SD_k σ)
private def InvFin (f : d.MF) : Prop := ∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X
private def InvInf (G : d.MF) : Prop := ∀ X Z, finOne F • Z = 0 → G (X + Z) = G X
private def fcrd (X : d.MxE) : d.Af3 := fun k => (d.crd X k).2
private def StepF (x : d.G) (A B : d.MF → d.MF) : Prop :=
  (∀ f, InvFin d f → InvFin d (A f)) ∧ ∀ G, InvInf d G → InvInf d (B G) ∧
    ∀ f, InvFin d f → ∀ Φ ∈ d.sch, d.T Φ = (fun X => f X * G X) → d.T (d.om x Φ) = fun X => A f X * B G X
private theorem step_comp {x x' : d.G} {A A' B B' : d.MF → d.MF} (h : StepF d x A B) (h' : StepF d x' A' B') :
    StepF d (x * x') (A ∘ A') (B ∘ B') :=
  ⟨fun f hf => h.1 _ (h'.1 f hf), fun G hG => ⟨(h.2 _ (h'.2 G hG).1).1, fun f hf Φ hΦ hT => by
    rw [map_mul, mul_apply_eq_comp]
    exact (h.2 (B' G) (h'.2 G hG).1).2 (A' f) (h'.1 f hf) (d.om x' Φ) (d.om_sch x' Φ hΦ) ((h'.2 G hG).2 f hf Φ hΦ hT)⟩⟩
private theorem step_conj (hT : TAll_k) {x₁ x₂ x' : d.G} {A₁ A₂ B₁ B₂ B' : d.MF → d.MF}
    (h₁ : StepF d x₁ A₁ B₁) (h₂ : StepF d x₂ A₂ B₂) (h' : StepF d x' id B') (h1 : x₁ * x₂ = 1) :
    ∃ B, StepF d (x₁ * x' * x₂) id B := by
  have hc := step_comp d (step_comp d h₁ h') h₂; have h0 := step_comp d h₁ h₂
  refine ⟨fun G => if h : ∃ X₀, G X₀ ≠ 0 ∧ B₁ (B₂ G) X₀ ≠ 0 then
      (G h.choose / B₁ (B₂ G) h.choose) • B₁ (B' (B₂ G)) else 0,
    fun _ hf => hf, fun G hG => ⟨?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · dsimp only; split_ifs with h
    · exact fun X Z hZ => by simp only [Pi.smul_apply, smul_eq_mul]; congr 1; exact (hc.2 G hG).1 X Z hZ
    · exact fun _ _ _ => rfl
  · have e0 := (h0.2 G hG).2 f hf Φ hΦ hTΦ; rw [h1, map_one, one_apply_eq_self, hTΦ] at e0
    exact conj_split d hT id hΦ hTΦ ((hc.2 G hG).2 f hf Φ hΦ hTΦ) fun X Y => by
      have hW1 : eInf F • X + finOne F • Y = X + finOne F • (Y - X) := by
        rw [show X + finOne F • (Y - X) = (eInf F • X + finOne F • X) + finOne F • (Y - X) by rw [smul_split],
          smul_sub]; abel
      have hW2 : eInf F • X + finOne F • Y = Y + eInf F • (X - Y) := by
        rw [show Y + eInf F • (X - Y) = (eInf F • Y + finOne F • Y) + eInf F • (X - Y) by rw [smul_split],
          smul_sub]; abel
      have e := congrFun e0 (eInf F • X + finOne F • Y)
      rw [hW1, hf X _ (fun w => cw_finOne d w _), (h0.1 f hf) X _ (fun w => cw_finOne d w _), ← hW1, hW2,
        hG Y _ (by rw [smul_smul, finOne_mul_eInf, zero_smul]),
        (h0.2 G hG).1 Y _ (by rw [smul_smul, finOne_mul_eInf, zero_smul])] at e; exact e
private theorem stepN_f (hT : TAll_k) (x : d.G) (β : d.Mn) (hx : inFrame d.b x = fromBlocks 1 β 0 1)
    (hβ : eInf F • β = 0) : StepF d x id (fun G X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) * G X) := by
  have hβ' : β = finOne F • β := by conv_lhs => rw [← smul_split β, hβ, zero_add]
  have hβM (M : d.Mn) (hM : finOne F • M = 0) : β * M = 0 := by
    rw [hβ', Matrix.smul_mul, ← Matrix.mul_smul, hM, Matrix.mul_zero]
  refine ⟨fun _ hf => hf, fun G hG => ⟨fun X Z hZ => ?_, fun f _ Φ hΦ hTΦ => ?_⟩⟩
  · show d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram (X + Z) (X + Z)))) * G (X + Z) = _
    rw [hG X Z hZ, show β * d.gram (X + Z) (X + Z) = β * d.gram X X by
      rw [gram_add_l, gram_add_r, gram_add_r, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
        hβM (d.gram X Z) (by rw [← gram_smul_r, hZ]; simp [SD_k.gram]),
        hβM (d.gram Z X) (by rw [← gram_smul_l, hZ]; simp [SD_k.gram]),
        hβM (d.gram Z Z) (by rw [← gram_smul_l, hZ]; simp [SD_k.gram])]; simp]
  · funext X; rw [(hT.2.1 F E σ d Φ hΦ).1 x β hx X, hTΦ]; simp only [id]; ring
private theorem stepM_f (hT : TAll_k) (x : d.G) (a a' : d.Gn) (hx : inFrame d.b x = fromBlocks a.1 0 0 a'.1)
    (ha : eInf F • a'.1 = eInf F • (1 : d.Mn)) : ∃ B, StepF d x id B := by
  set M : d.Mn := (a'⁻¹).1
  have hMe : eInf F • M = eInf F • (1 : d.Mn) := by
    calc eInf F • M = (eInf F • a'.1) * M := by rw [ha, Matrix.smul_mul, Matrix.one_mul]
      _ = eInf F • (1 : d.Mn) := by rw [Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨fun G X => (d.χ a.det : ℂ) * (((absE F E a.det : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) * G (X * Mᵀ),
    fun _ hf => hf, fun G hG => ⟨fun X Z hZ => ?_, fun f hf Φ hΦ hTΦ => ?_⟩⟩
  · show _ * G ((X + Z) * Mᵀ) = _; rw [Matrix.add_mul, hG _ _ (by rw [← Matrix.smul_mul, hZ, Matrix.zero_mul])]
  · funext X; rw [(hT.2.1 F E σ d Φ hΦ).2.1 x a a' hx X, hTΦ]
    have hf' : f (X * Mᵀ) = f X := by
      rw [show X * Mᵀ = X + X * (M - 1)ᵀ by
        rw [Matrix.transpose_sub, transpose_one, Matrix.mul_sub, Matrix.mul_one]; abel]
      exact hf X _ ((cw_zero_iff d _).2 (by
        rw [← Matrix.mul_smul, Matrix.transpose_sub, smul_sub, ← Matrix.transpose_smul, ← Matrix.transpose_smul,
          hMe, sub_self, Matrix.mul_zero]))
    beta_reduce; rw [hf']; simp only [id]; ring
private def kerSub (c : AF F) : AddSubgroup d.MxE where
  carrier := {Z | c • Z = 0}
  add_mem' ha hb := by simp only [Set.mem_ofPred_eq] at *; rw [smul_add, ha, hb, add_zero]
  zero_mem' := by simp
  neg_mem' ha := by simp only [Set.mem_ofPred_eq] at *; rw [smul_neg, ha, neg_zero]
private theorem stepW_f (hT : TAll_k) (hA : SiegelWeilDatumProperties) (ε : ℤˣ) (w : d.G) (hw : d.IsW ε w) :
    ∃ A B, StepF d w A B := by
  obtain ⟨⟨ν, hν⟩, -, -⟩ := hA F E σ d; have := hν.1; obtain ⟨_, _, _, _⟩ := KFock.mxTop_k d
  have hsm (c : AF F) : Continuous fun Z : d.MxE => c • Z := continuous_const_smul c
  let VI := kerSub d (finOne F); let VF := kerSub d (eInf F)
  have hlc (c : AF F) : LocallyCompactSpace (kerSub d c) :=
    (isClosed_eq (hsm c) continuous_const).isClosedEmbedding_subtypeVal.locallyCompactSpace
  have := hlc (finOne F); have := hlc (eInf F)
  have : SecondCountableTopology VI := TopologicalSpace.Subtype.secondCountableTopology (VI : Set d.MxE)
  have : SecondCountableTopology VF := TopologicalSpace.Subtype.secondCountableTopology (VF : Set d.MxE)
  have : BorelSpace VI := Subtype.borelSpace _; have : BorelSpace VF := Subtype.borelSpace _
  have h₁ (Z : d.MxE) : eInf F • Z ∈ VI := by change finOne F • _ = 0; rw [smul_smul, finOne_mul_eInf, zero_smul]
  have h₂ (Z : d.MxE) : finOne F • Z ∈ VF := by change eInf F • _ = 0; rw [smul_smul, eInf_mul_finOne, zero_smul]
  let Φs : VI × VF ≃ₜ+ d.MxE :=
    { toFun p := p.1.1 + p.2.1
      invFun Z := (⟨eInf F • Z, h₁ Z⟩, ⟨finOne F • Z, h₂ Z⟩)
      left_inv := fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => Prod.ext
        (Subtype.ext <| by show eInf F • (a + b) = a; rw [smul_add, show eInf F • b = 0 from hb, add_zero]
                           conv_rhs => rw [← smul_split a]; rw [show finOne F • a = 0 from ha, add_zero])
        (Subtype.ext <| by show finOne F • (a + b) = b; rw [smul_add, show finOne F • a = 0 from ha, zero_add]
                           conv_rhs => rw [← smul_split b]; rw [show eInf F • b = 0 from hb, zero_add])
      right_inv := smul_split
      map_add' p q := by show p.1.1 + q.1.1 + (p.2.1 + q.2.1) = p.1.1 + p.2.1 + (q.1.1 + q.2.1); abel
      continuous_toFun := (continuous_subtypeVal.comp continuous_fst).add (continuous_subtypeVal.comp continuous_snd)
      continuous_invFun := ((hsm (eInf F)).subtype_mk h₁).prodMk ((hsm (finOne F)).subtype_mk h₂) }
  obtain ⟨C, -, hC⟩ := KFock.integral_split ν (Measure.addHaar : Measure VI) (Measure.addHaar : Measure VF) Φs
  refine ⟨fun f X => (C : ℂ) * ∫ a : VI, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X a.1)) * f a.1 ∂Measure.addHaar,
    fun G X => ∫ b : VF, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X b.1)) * G b.1 ∂Measure.addHaar,
    fun f _ X Z hZ => by
      have hZ' := (cw_zero_iff d Z).1 hZ
      have eZ : Z = finOne F • Z := by conv_lhs => rw [← smul_split Z, hZ', zero_add]
      dsimp only; congr 2; funext a
      rw [gram_add_l, show d.gram Z a.1 = 0 by
        rw [eZ, gram_smul_l, ← gram_smul_r, show finOne F • a.1 = 0 from a.2, SD_k.gram,
          Matrix.map_zero _ (map_zero _), Matrix.mul_zero], add_zero],
    fun G hG => ⟨fun X Z hZ => by
      dsimp only; congr 1; funext b
      have eb : b.1 = finOne F • b.1 := by conv_lhs => rw [← smul_split b.1, show eInf F • b.1 = 0 from b.2, zero_add]
      rw [gram_add_l, show d.gram Z b.1 = 0 by
        rw [eb, gram_smul_r, ← gram_smul_l, hZ, SD_k.gram, Matrix.transpose_zero, Matrix.zero_mul,
          Matrix.zero_mul], add_zero],
    fun f hf Φ hΦ hTΦ => funext fun X => by
      rw [hT.2.2.1 F E σ d ν hν ε w hw Φ hΦ X, hTΦ, hC]
      have hpt : (fun p : VI × VF => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Φs p))) * (f (Φs p) * G (Φs p))) =
          fun p => (d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X p.1.1)) * f p.1.1) *
            (d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X p.2.1)) * G p.2.1) := funext fun p => by
        have hf' : f (p.1.1 + p.2.1) = f p.1.1 := hf p.1.1 p.2.1 ((cw_zero_iff d _).2 p.2.2)
        have hG' : G (p.1.1 + p.2.1) = G p.2.1 := by rw [add_comm]; exact hG p.2.1 p.1.1 p.1.2
        rw [show Φs p = p.1.1 + p.2.1 from rfl, hf', hG', gram_add_r,
          show ∀ M M', d.tt (M + M') = d.tt M + d.tt M' from fun _ _ => by
            simp only [SD_k.tt, trace_add, map_add (f := _)], mul_add, AddChar.map_add_eq_mul]; ring
      rw [hpt, integral_prod_mul (μ := (Measure.addHaar : Measure VI)) (ν := (Measure.addHaar : Measure VF))
        (fun a : VI => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X a.1)) * f a.1)
        (fun b : VF => d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X b.1)) * G b.1)]; ring⟩⟩
private theorem finAct_step (hT : TAll_k) (x : d.G) {B : d.MF → d.MF} (hB : StepF d x id B) :
    ∀ g ∈ SB d.Af3, ∃ g' ∈ SB d.Af3, ∀ f : d.MF, (∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X) →
      ∀ Φ ∈ d.sch, d.T Φ = (fun X => f X * g fun k => (d.crd X k).2) →
        d.T (d.om x Φ) = fun X => f X * g' fun k => (d.crd X k).2 := by
  intro g hg; set G : d.MF := fun X => g (fcrd d X)
  have hG : InvInf d G := fun X Z hZ => congrArg g (funext fun k => by
    show (d.crd (X + Z) k).2 = (d.crd X k).2; rw [KFock.crd_add_k]
    change (d.crd X k).2 + (d.crd Z k).2 = _; rw [KFock.crd_fin_k d Z hZ k, add_zero])
  have hBG := (hB.2 G hG).1
  set g₁ : d.Af3 → ℂ := fun y => B G (d.cmb fun k => pairA F 0 (y k))
  have hBg (X) : B G X = g₁ (fcrd d X) := by
    set Y := d.cmb fun k => pairA F 0 (fcrd d X k)
    have hp (c : AF F) : finOne F * c = pairA F 0 c.2 := Prod.ext (finOne_fst_mul c) (finOne_snd_mul c)
    have hcmbs (c : AF F) (y : d.I3 → AF F) : d.cmb (fun k => c * y k) = c • d.cmb y := by
      ext _ _; simp only [SD_k.cmb, Matrix.smul_apply, Finset.smul_sum]
      exact Finset.sum_congr rfl fun _ _ => by rw [TensorProduct.smul_tmul', smul_eq_mul]
    have e1 : finOne F • X = Y := by
      conv_lhs => rw [← KFock.cmb_crd_k d X]
      rw [← hcmbs]; exact congrArg d.cmb (funext fun _ => hp _)
    have e2 : finOne F • Y = Y := by rw [← hcmbs]; exact congrArg d.cmb (funext fun _ => hp _)
    have h := hBG Y (X - Y) (by rw [smul_sub, e1, e2, sub_self]); rwa [add_sub_cancel] at h
  by_cases hg0 : g = 0
  · refine ⟨0, (SB _).zero_mem, fun f _ Φ hΦ hTΦ => ?_⟩
    rw [d.T_inj hT Φ hΦ (funext fun _ => by simp [hTΦ, hg0]), map_zero, d.T_zero]; funext _; simp
  refine ⟨g₁, ?_, fun f hf Φ hΦ hTΦ => by rw [(hB.2 G hG).2 f hf Φ hΦ hTΦ]; funext X; simp only [id, hBg]; rfl⟩
  obtain ⟨φ, v₀, hv₀⟩ := exists_schwartz_ne (κ := d.I3) F
  set f₀ : d.MF := fun X => φ fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1
  have hf₀ : InvFin d f₀ := fun X Z hZ => congrArg φ (funext fun k => by
    have : (d.crd Z k).1 = 0 := by rw [← eInf_fst_mul (d.crd Z k), ← crd_smul, (cw_zero_iff d Z).1 hZ]; simp [SD_k.crd]
    rw [KFock.crd_add_k]; change InfiniteAdeleRing.ringEquiv_mixedSpace F ((d.crd X k).1 + (d.crd Z k).1) = _
    rw [this, add_zero])
  have hmem : (fun X => f₀ X * G X) ∈ d.schM := by
    show (fun c => f₀ (d.cmb c) * G (d.cmb c)) ∈ schA F d.I3
    rw [show (fun c => f₀ (d.cmb c) * G (d.cmb c)) = pureA F (⇑φ) g from funext fun c => by
      show (φ fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd (d.cmb c) k).1) *
        g (fun k => (d.crd (d.cmb c) k).2) = _; rw [KFock.crd_cmb_k]; rfl]
    exact Submodule.subset_span ⟨φ, g, hg, rfl⟩
  obtain ⟨Φ₀, hΦ₀, hTΦ₀⟩ := (hT.1 F E σ d).2.1 _ hmem
  have hm := (hT.1 F E σ d).1 _ (d.om_sch x Φ₀ hΦ₀); rw [(hB.2 G hG).2 f₀ hf₀ Φ₀ hΦ₀ hTΦ₀] at hm
  have hs := slice_mem _ hm (fun k => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v₀ k))
  have e2 : (fun y : d.Af3 => (fun X => id f₀ X * B G X)
      (d.cmb fun k => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v₀ k)) (y k))) =
      φ v₀ • g₁ := funext fun y => by
    simp only [id, Pi.smul_apply, smul_eq_mul, hBg,
      show fcrd d (d.cmb fun k => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v₀ k)) (y k)) = y from
        funext fun k => by simp only [fcrd, KFock.crd_cmb_k]; rfl]
    congr 1; show (φ fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd (d.cmb _) k).1) = _
    rw [KFock.crd_cmb_k]; congr 1; funext k; exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (v₀ k)
  have := (SB d.Af3).smul_mem (φ v₀)⁻¹ (e2 ▸ hs); rwa [smul_smul, inv_mul_cancel₀ hv₀, one_smul] at this
end FinStep
end W
theorem awayAct_of_tAll_k (hT : TAll_k) : AwayAct_k := fun F E _ _ _ _ _ σ d R w x hx => by
  have hA := kfour.auxiliaryExistence_holds; obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  obtain ⟨x₁, x₂, x₃, x₄, t, c, b, a, a', hxe, h1, h2, h3, h4, ht, hc, hb, -, ha'⟩ :=
    W.adDecomp d ε w₀ hw₀ (eW w) (eW_mul_self w) x ((W.eW_smul_eq_iff d w _ _).2 (by rw [hx, Krd.cw_one_k]))
  obtain ⟨C, s, BW, -, hW⟩ := R.stepW w hT hA ε w₀ hw₀
  have hW3 := R.step_comp w d.om_sch (R.step_comp w d.om_sch hW hW) hW
  obtain ⟨BC, hC⟩ := W.away_conj R w hT hW hW3 (W.stepN R w hT x₂ c h2 hc)
    (by simpa only [mul_assoc] using RD_k.w_four hw₀)
  have hall := R.step_comp w d.om_sch (R.step_comp w d.om_sch (R.step_comp w d.om_sch
    (W.stepN R w hT x₁ t h1 ht) hC) (W.stepM R w hT x₃ a a' h3 ha')) (W.stepN R w hT x₄ b h4 hb)
  rw [hxe, (eq_inv_of_mul_eq_one_left (RD_k.w_four hw₀)).symm]
  exact ⟨_, fun Ψ hΨ => ⟨(hall.2 Ψ hΨ).1, fun f hf Φ hΦ hTΦ => (hall.2 Ψ hΨ).2 f hf Φ hΦ hTΦ⟩⟩
theorem finAct_of_tAll_k (hT : TAll_k) : FinAct_k := fun F E _ _ _ _ _ σ d x hx => by
  have hA := kfour.auxiliaryExistence_holds; obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  have he : eInf F • inFrame d.b x = eInf F • (1 : d.Mn2) := Place.cw_ext_k d
    (fun w => by rw [W.cw_eInf, W.cw_eInf, hx w, Krd.cw_one_k])
    (by rw [smul_smul, smul_smul, finOne_mul_eInf, zero_smul, zero_smul])
  obtain ⟨x₁, x₂, x₃, x₄, t, c, b, a, a', hxe, h1, h2, h3, h4, ht, hc, hb, -, ha'⟩ :=
    W.adDecomp d ε w₀ hw₀ (eInf F) eInf_mul_self x he
  obtain ⟨AW, BW, hW⟩ := W.stepW_f d hT hA ε w₀ hw₀
  have hW3 := W.step_comp d (W.step_comp d hW hW) hW
  obtain ⟨BC, hC⟩ := W.step_conj d hT hW hW3 (W.stepN_f d hT x₂ c h2 hc)
    (by simpa only [mul_assoc] using RD_k.w_four_pf hw₀)
  obtain ⟨BM, hM⟩ := W.stepM_f d hT x₃ a a' h3 ha'
  have hall := W.step_comp d (W.step_comp d (W.step_comp d
    (W.stepN_f d hT x₁ t h1 ht) hC) hM) (W.stepN_f d hT x₄ b h4 hb)
  rw [hxe, (eq_inv_of_mul_eq_one_left (RD_k.w_four_pf hw₀)).symm]
  exact W.finAct_step d hT _ hall
end KAway
private theorem ok_of_conj {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (hT : TAll_k) {y y' : GR d.n} {x₁ x₂ : d.G}
    {A₁ A₂ A' : d.LF → d.LF} {B₁ B₂ : d.MF → d.MF} (h₁ : R.StepOK w x₁ A₁ B₁) (h₂ : R.StepOK w x₂ A₂ B₂)
    (h' : R.StepOK w (R.ι w y') A' id) (hy : R.ι w y = x₁ * R.ι w y' * x₂) (h1 : x₁ * x₂ = 1) : R.OkY w y := by
  have hc := R.step_comp w d.om_sch (R.step_comp w d.om_sch h₁ h') h₂; have h0 := R.step_comp w d.om_sch h₁ h₂
  intro f hf
  by_cases hf0 : ∀ u, f u = 0
  · refine ⟨0, ⟨0, by ext; simp⟩, fun Ψ _ Φ hΦ hTΦ => ?_⟩
    rw [d.T_inj hT Φ hΦ (funext fun X => by simp [hTΦ, RD_k.tens, hf0]), map_zero, d.T_zero]
    funext X; simp [RD_k.tens]
  · push Not at hf0; obtain ⟨u₀, hu₀⟩ := hf0
    by_cases hex : ∃ κ : ℂ, κ ≠ 0 ∧ A₁ (A₂ f) = κ • f
    · obtain ⟨κ, hκ, hA⟩ := hex
      refine ⟨κ⁻¹ • A₁ (A' (A₂ f)), ?_, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
      · obtain ⟨φ, hφ⟩ := hc.1 f hf
        exact ⟨κ⁻¹ • φ, funext fun u => by simp [show φ u = A₁ (A' (A₂ f)) u from congrFun hφ u]⟩
      · have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ; rw [h1, map_one, one_apply_eq_self, hTΦ] at e0
        have hB (X) : B₁ (B₂ Ψ) X = κ⁻¹ * Ψ X := by
          obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u₀; have h2 := congrFun e0 (X + Z)
          simp only [RD_k.tens, Function.comp_apply, hZ3, hA, Pi.smul_apply, smul_eq_mul,
            hΨ X Z hZ1 hZ2, (h0.2 Ψ hΨ).1 X Z hZ1 hZ2] at h2
          rw [eq_inv_mul_iff_mul_eq₀ hκ]; apply mul_left_cancel₀ hu₀; linear_combination -h2
        rw [hy, (hc.2 Ψ hΨ).2 f hf Φ hΦ hTΦ]; funext X
        simp only [RD_k.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hB]; ring
    · refine ⟨0, ⟨0, by ext; simp⟩, fun Ψ hΨ Φ hΦ hTΦ => ?_⟩
      have hΨ0 (X) : Ψ X = 0 := by
        by_contra hX₀; have e0 := (h0.2 Ψ hΨ).2 f hf Φ hΦ hTΦ; rw [h1, map_one, one_apply_eq_self, hTΦ] at e0
        have key (u) : f u * Ψ X = A₁ (A₂ f) u * B₁ (B₂ Ψ) X := by
          obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u
          simpa only [RD_k.tens, Function.comp_apply, hZ3, hΨ X Z hZ1 hZ2, (h0.2 Ψ hΨ).1 X Z hZ1 hZ2] using
            congrFun e0 (X + Z)
        have hB0 : B₁ (B₂ Ψ) X ≠ 0 := fun h0' => mul_ne_zero hu₀ hX₀ (by simpa [h0'] using key u₀)
        exact hex ⟨Ψ X / B₁ (B₂ Ψ) X, div_ne_zero hX₀ hB0, funext fun u => by
          have := key u; simp only [Pi.smul_apply, smul_eq_mul]; rw [div_mul_eq_mul_div, eq_div_iff hB0]
          linear_combination -this⟩
      have : Φ = 0 := d.T_inj hT Φ hΦ (by rw [hTΦ]; funext X; simp [RD_k.tens, hΨ0])
      subst this; rw [map_zero, d.T_zero]; funext X; simp [RD_k.tens, hΨ0]
theorem locOpEx_of_tAll_k (hT : TAll_k) : LocOpEx_k := fun F E _ _ _ _ _ σ d R w => by
  have hA := kfour.auxiliaryExistence_holds; refine ⟨_, R.isLocOp_of_ok w fun y => ?_⟩
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d; obtain ⟨C, s, B, -, hW⟩ := R.stepW w hT hA ε w₀ hw₀
  obtain ⟨y1, y2, y3, y4, hy, ⟨t, ht⟩, ⟨c, hc, hc2⟩, ⟨a, ha, ha2⟩, ⟨b, hb, hb2⟩⟩ := Glob.decomp d.n y
  obtain ⟨y', hy', hrel⟩ := R.oppositeUnipotent_weylConj w hw₀ y2 c hc hc2
  have hx : ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)ᴴ = (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c := by
    rw [conjTranspose_smul, hc, show star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ by
      rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp [Complex.inv_I]]
  rw [hy]; exact R.ok_mul w d.om_sch (R.ok_mul w d.om_sch (R.ok_mul w d.om_sch
    (R.ok_of_step w (R.stepN w hT y1 _ (herm_smul_one' t) ht))
    (ok_of_conj R w hT (R.step_comp w d.om_sch (R.step_comp w d.om_sch hW hW) hW) hW
      (R.stepN w hT y' _ hx hy') hrel (RD_k.w_four hw₀)))
    (let ⟨_, _, hc⟩ := R.stepM w hT y3 a ha ha2; R.ok_of_step w hc))
    (R.ok_of_step w (R.stepN w hT y4 b hb hb2))
end PositivityTheory.SiegelWeilFormula
end
