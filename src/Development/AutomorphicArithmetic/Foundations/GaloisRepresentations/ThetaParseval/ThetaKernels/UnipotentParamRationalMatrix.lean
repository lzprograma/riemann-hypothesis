module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilMeasdictToMx
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.COneLawPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneDilV
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneSmulAdr
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.SectionDilationExp
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.NormInvMulSelf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.RelReal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ExistsRationalMatrixUnipotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled

/-! # UnipotentParamRationalMatrix: Consolidated global theta-kernel definitions and proofs (UnipotentParamRationalMatrix). -/
@[expose] public section

noncomputable section
open PositivityTheory.SiegelWeilFormula
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw
open Complex (exp)
open GlobalTheory.Eis (cosetSum term)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section
namespace PositivityTheory.SiegelWeilFormula.KWhit
def RelAlg_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : SD_k σ), ∃ (η : E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n),
    η ≠ 0 ∧ (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) ∧
    (∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)) ∧
    (∀ y : Fin d.m → E, HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd_k d η) y y = 0 → y = 0) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (Jd_k d η) ∧
    ∀ T : nF σ d.Y d.b, IsND T → ∃ T₀ : Matrix (Fin d.n) (Fin d.n) E, T.1.1 = incM F T₀ ∧
      (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧ (Td η T₀).det ≠ 0
end PositivityTheory.SiegelWeilFormula.KWhit
end

section
open scoped Classical ComplexOrder
open GlobalTheory.Doubling (absE)
open Matrix (isUnit_iff_isUnit_det)
variable {σ : E →ₐ[F] E}
section
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
theorem isCharAF_of_good_k (B : Base F E)
    (hB : _root_.UpperTheory.TP.W.GoodK σ B) : HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F B.ψ :=
  GlobalTheory.StdCharFromIsStd.isCharAF hB.std
section
variable {d : SD_k σ}
theorem frW_det_k (R : RD_k d) {η : E} (hη : η ≠ 0) (w : InfinitePlace F) :
    IsUnit (cW d.B η w • (R.fr w).1.map star).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_smul]
  refine mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_
  have hu : IsUnit (R.fr w).1.det := (isUnit_iff_isUnit_det _).1 (R.fr w).isUnit
  have e : ((R.fr w).1.map star).det = star (R.fr w).1.det := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose ((R.fr w).1)ᴴ]; rfl
  rw [e, star_ne_zero]
  exact hu.ne_zero
def frW_k (R : RD_k d) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) : d.Gmc :=
  Matrix.nonsingInvUnit (cW d.B η w • (R.fr w).1.map star) (frW_det_k R hη w)
theorem frW_frc_k (R : RD_k d) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) :
    (frW_k R η hη w).1 = cW d.B η w • (R.fr w).1.map star := rfl
end
section
variable (d : SD_k σ)
theorem gW_det_k (u : d.Gn) {η : E} (hη : η ≠ 0) (w : InfinitePlace F) :
    IsUnit (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_smul]
  refine mul_ne_zero (pow_ne_zero _ (cW_ne d.B hη w)) ?_
  have hu : IsUnit u.1.det := (isUnit_iff_isUnit_det _).1 u.isUnit
  have h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det := by
    unfold SD_k.cw; rw [RingHom.map_det]; rfl
  have h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det := by
    rw [← Matrix.det_conjTranspose]; rfl
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', h2, h1]
  exact inv_ne_zero (star_ne_zero.2 (hu.map (piInf (d.B.emb w))).ne_zero)
def gW_k (u : d.Gn) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) : d.Gnc :=
  Matrix.nonsingInvUnit (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹) (gW_det_k d u hη w)
theorem gW_gc_k (u : d.Gn) (η : E) (hη : η ≠ 0) (w : InfinitePlace F) :
    (gW_k d u η hη w).1 * ((d.cw w u.1)ᵀ).map star = cW d.B η w • 1 := by
  have hu : IsUnit u.1.det := (isUnit_iff_isUnit_det _).1 u.isUnit
  have hN : IsUnit (((d.cw w u.1)ᵀ).map star).det := by
    have h1 : (d.cw w u.1).det = piInf (d.B.emb w) u.1.det := by
      unfold SD_k.cw; rw [RingHom.map_det]; rfl
    have h2 : (((d.cw w u.1)ᵀ).map star).det = star (d.cw w u.1).det := by
      rw [← Matrix.det_conjTranspose]; rfl
    rw [h2, h1, isUnit_iff_ne_zero, star_ne_zero]
    exact (hu.map (piInf (d.B.emb w))).ne_zero
  change (cW d.B η w • (((d.cw w u.1)ᵀ).map star)⁻¹) * ((d.cw w u.1)ᵀ).map star = cW d.B η w • 1
  rw [Matrix.smul_mul, Matrix.nonsing_inv_mul _ hN]
end
def εsW_k {d : SD_k σ} (R : RD_k d) (η : E) (w : InfinitePlace F) (_ : Fin d.m) : Bool :=
  decide (0 < (((d.B.emb w).1 η / R.ζ) * ((R.sg w : ℤ) : ℂ)).re)
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end

section
namespace PositivityTheory.SiegelWeilFormula.AStep
structure Hyps_k : Prop where
  holLead : HolLead
  holT : HolT
  tAll : TAll_k
  thetaCoef : ThetaCoef_k
  auxEx : SiegelWeilDatumProperties
  coefEx : CoefEx_k
  fockMem : FockMem_k
  liftEx : LiftEx_k
  locOpEx : LocOpEx_k
  locInst : LocInst_k
  gSplit : GSplit_k
  polyKFin : PolyKFin_k
  secK : SecK_k
  eisWk : EisWk_k
  lamBd : LamBd_k
  lamSing : LamSing_k
  fourierZero : FourierZero_k
  unfold : Unfold_k
  whitLow : WhitLow_k
  vacK : VacK_k
  iwaQ : IwaQ_k
  cTSplit : CTSplit_k
  uEx : UEx_k
  fcConj : FcConj_k
  orbRes : OrbRes_k
variable {σ : E →ₐ[F] E}
section
variable (d : SD_k σ)
def EData_k (f : d.G → ℂ) (s₁ s₀ : ℂ) (U : Set ℂ) (p : Polynomial ℂ) (Ê : ℂ → d.G → ℂ) (t : ℝ) : Prop :=
  IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ p ≠ 0 ∧
    (∀ g, DifferentiableOn ℂ (Ê · g) U) ∧ ContinuousOn (fun y : ℂ × d.G => Ê y.1 y.2) (U ×ˢ Set.univ) ∧
    (∀ z ∈ U, ∀ γ ∈ d.r2, ∀ g, Ê z (γ * g) = Ê z g) ∧
    ∀ z : ℂ, t < z.re → (∀ C : Set d.G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets d.p2 d.r2 → ℝ,
        Summable u ∧
        ∀ g ∈ C, ∀ q, ‖term d.p2 d.r2 (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) *
            f x) g q‖ ≤ u q) ∧
      ∀ g, Ê z g = p.eval z * d.eis f s₁ z g
def avg_k (L : LD_k d) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E)) (𝓤 : Set (Fin L.n →
    AE F E))
    (nb : d.nA_ → d.G) (lam : Measure d.nA_) (𝓖 : Set d.nA_) (φ : d.G → ℂ) (T : d.nF_)
    (x : d.G) : ℂ :=
  ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) ∂ν
def cOne_k (L : LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb' : nA σ L.Y L.b → L.sd.G) (lam' : Measure
    (nA σ L.Y L.b))
    (𝓖' : Set (nA σ L.Y L.b)) (T' : nF σ L.Y L.b) (x : d.G) : ℂ :=
  fc d.B.ψ L.b nb' lam' 𝓖' (cosetSum (par2 σ L.Y) (rat2 σ L.Y) fun g =>
    ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) T' 1
end
def fcAll_k (d : SD_k σ) {nb lam 𝓖} (hc : d.CD nb lam 𝓖) (T : d.nF_) (x : d.G) :=
  kfour.fcAll_core_k d hc T x
theorem fcCont_k (d : SD_k σ) {nb lam 𝓖} (hc : d.CD nb lam 𝓖) (T : d.nF_) (f : d.G →
    ℂ)
    (hf : Continuous f) (hi : ∀ γ ∈ d.r2, ∀ g, f (γ * g) = f g) : Continuous fun x =>
        fc d.B.ψ d.b nb lam 𝓖 f T x := by
  obtain ⟨hnb, hlam, hfd, hvol⟩ := hc
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := kfour.sigma_sigma_of_good_k hB
  have hb := d.ok.frame
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ hb
  obtain ⟨iTG, iLCG, -, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  have hcont := kfour.nb_continuous hσ hb hnb
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ hb
  set χ : d.nA_ → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
    with hχ
  have hχc : Continuous χ := kfour.continuous_chr hψ.1 T.1.1
  have hχn : ∀ β, ‖χ β‖ = 1 := fun β => hψ.2.1 _
  have hfin : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  have hmul := (hcont.comp continuous_fst).mul continuous_snd
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨N, hN, hNx⟩ := exists_compact_mem_nhds x₀
  have hKN := (hK.prod hN).image hmul
  obtain ⟨M, hM⟩ := hKN.exists_bound_of_continuousOn hf.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((hf.comp (hcont.mul continuous_const)).mul hχc).aestronglyMeasurable
  · filter_upwards [hNx] with x hx
    refine Filter.Eventually.of_forall fun β => ?_
    obtain ⟨γ, hγ, hk⟩ := hKc β
    rw [norm_mul, hχn β, mul_one]
    have : f (nb β * x) = f (nb (γ + β) * x) := by
      rw [kfour.nb_add hnb, mul_assoc, hi _ (kfour.nb_rat hnb γ hγ)]
    rw [this]
    exact hM _ ⟨(γ + β, x), ⟨hk, hx⟩, rfl⟩
  · exact Filter.Eventually.of_forall fun β =>
      ((hf.comp (continuous_const.mul continuous_id)).mul continuous_const).continuousAt
end PositivityTheory.SiegelWeilFormula.AStep
end

section
namespace PositivityTheory.SiegelWeilFormula.AStep
theorem chi_adrU_k (d : SD_k σ) (w : InfinitePlace F) (τ : ℝ) :
    have := d.cm.1
    (d.χ (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : ℂ) = 1 := by
  have := d.cm.1
  have : Nontrivial (AF F) := (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  have : StrongRankCondition (AF F) := commRing_strongRankCondition _
  have hfr : Module.finrank (AF F) (AE F E) = 2 := by
    rw [Module.finrank_baseChange]; exact d.cm.2.2.1
  have hmem : adrU w τ ∈ (Units.map (Algebra.norm (AF F) : AE F E →* AF F)).range := by
    refine ⟨Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w (τ / 2)), Units.ext ?_⟩
    show Algebra.norm (AF F) (algebraMap (AF F) (AE F E) (adr w (Real.exp (τ / 2)))) = adr w (Real.exp τ)
    rw [Algebra.norm_algebraMap, hfr, sq, adr_mul, ← Real.exp_add, add_halves]
  have := d.ok.res (adrU w τ)
  rw [ite_eq_left (Subgroup.mem_sup_right hmem)] at this
  exact this
end PositivityTheory.SiegelWeilFormula.AStep
end

section
namespace PositivityTheory.SiegelWeilFormula.AStep
theorem inFrame_dil_k {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) : inFrame d.b (R.ι w y) = Matrix.diagonal (dilV d.cm w i₀ τ) := by
  have := d.cm.1
  refine Place.mat_ext d.cm d.B.emb (fun u => ?_) ?_
  · have hD : (Matrix.diagonal (dilV d.cm w i₀ τ)).map (piInf (d.B.emb u)) =
        Matrix.diagonal (fun k => piInf (d.B.emb u) (dilV d.cm w i₀ τ k)) := Matrix.diagonal_map (map_zero _)
    rw [hD]
    simp_rw [piInf_dilV d.cm d.B.emb w u i₀ τ]
    by_cases hu : u = w
    · subst hu
      simp only [ite_true]
      have hat := R.at_w u y
      have hζ : R.ζ ≠ 0 := by
        rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
        · exact one_ne_zero
        · exact Complex.I_ne_zero
      have hZ : dZ d.n R.ζ⁻¹ * dZ d.n R.ζ = 1 := by
        simp only [dZ, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero,
          add_zero, zero_add, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hζ, one_smul,
          smul_zero, Matrix.fromBlocks_one]
      have e1 : d.cw u (inFrame d.b (R.ι u y)) = dZ d.n R.ζ⁻¹ * (mR y * dZ d.n R.ζ) := by
        rw [← hat, ← Matrix.mul_assoc, hZ, Matrix.one_mul]
      show d.cw u _ = _
      rw [e1, hy, ← Matrix.fromBlocks_diagonal]
      simp only [dZ, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
        add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, one_smul, Matrix.one_mul,
        smul_zero, mul_inv_cancel₀ hζ]
    · simp only [ite_eq_right hu, Matrix.diagonal_one]
      exact R.off_w w u y hu
  · rw [R.off_f w y]
    ext i j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with hij
    · subst hij; exact (finOne_dilV d.cm w i₀ τ i).symm
    · rfl
end PositivityTheory.SiegelWeilFormula.AStep
end

section
namespace PositivityTheory.SiegelWeilFormula.AStep
theorem j_comm_dil_k {d : SD_k σ} (R : RD_k d) (L : LD_k d) (w : InfinitePlace F) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single L.i₀ 1) τ y) (g : L.sd.G) : L.j g * R.ι w y = R.ι w y * L.j g := by
  apply kfour.inFrame_injective d.b
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul,
      inFrame_dil_k R w L.i₀ τ y hy]
  ext u v
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hv : v ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set d.N2)
  · rw [((L.j_out g) v hv u).2, Matrix.one_apply]
    split_ifs with huv
    · subst huv; ring
    · simp
  · by_cases hu : u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set d.N2)
    · rw [((L.j_out g) u hu v).1, Matrix.one_apply]
      split_ifs with huv
      · subst huv; ring
      · simp
    · rw [dilV_off d.cm w L.i₀ τ u hu, dilV_off d.cm w L.i₀ τ v hv, one_mul, mul_one]
theorem l_eq_T_k (d : SD_k σ) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) : d.l Ψ = d.T Ψ 0 := by
  have h1 := d.ok.dbl.kill 0 Ψ hΨ
  have h2 : ∀ M : Matrix (Fin d.n) d.N2 (AE F E), (0 : d.MxE) * M = 0 :=
    fun M => Matrix.zero_mul M
  unfold SD_k.T
  rw [← h1]
  congr 2
  ext i j
  exact (congrFun (congrFun (Matrix.zero_mul (diagCols (Fin d.n))ᵀ) i) j).trans
    (congrFun (congrFun (Matrix.zero_mul (incM F d.b.1.toCols₂)ᵀ) i) j).symm
theorem inFrame_dil'_k {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    inFrame d.b (R.ι w y) = Matrix.fromBlocks (dilT d.cm w i₀ τ).1 0 0 (dilT d.cm w i₀ (-τ)).1 := by
  rw [inFrame_dil_k R w i₀ τ y hy]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.diagonal_apply, dilT, dilV]
theorem constantTerm_dilation (H : Hyps_k) {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ)
    (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (h : d.G) :
    d.sec0 Φ (R.ι w y * h) = Complex.exp (τ * d.m) * d.sec0 Φ h := by
  have := d.cm.1
  have hpres : ∀ x, ∀ Ψ ∈ d.sch, d.om x Ψ ∈ d.sch := d.ok.dbl.weil.2.1.pres
  have hΨ := hpres h Φ hΦ
  unfold SD_k.sec0
  rw [map_mul, mul_apply_eq_comp, l_eq_T_k d _ (hpres _ _ hΨ), l_eq_T_k d _ hΨ,
    ((H.tAll.2.1 F E σ d _ hΨ).2.1 (R.ι w y) (dilT d.cm w i₀ τ) (dilT d.cm w i₀ (-τ)) (inFrame_dil'_k R w i₀ τ y hy) 0),
    det_dilT, chi_adrU_k d w τ, absE_adrU d.cm w τ]
  have hz : ∀ M : d.Mn, d.T (d.om h Φ) ((0 : d.MxE) * M) = d.T (d.om h Φ) 0 :=
    fun M => congrArg _ (Matrix.zero_mul M)
  rw [hz, ← Real.exp_mul, Complex.ofReal_exp, one_mul]
  congr 2
  push_cast; ring
end PositivityTheory.SiegelWeilFormula.AStep
end

section
namespace PositivityTheory.SiegelWeilFormula.AStep
theorem a_dil_k {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) (h : d.G) : d.a (R.ι w y * h) = Real.exp (2 * τ) * d.a h ∧ 0 ≤ d.a h := by
  have := d.cm.1
  have hf := inFrame_dil'_k R w i₀ τ y hy
  have h21 : (inFrame d.b (R.ι w y)).toBlocks₂₁ = 0 := by rw [hf, Matrix.toBlocks_fromBlocks₂₁]
  obtain ⟨t, ht, hdet⟩ := Avac.isPar_of_frame_k d (R.ι w y) h21
  have hdetU : Matrix.GeneralLinearGroup.det t = Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ) := by
    rw [← det_dilT d.cm w i₀ τ]
    apply Units.ext
    rw [hdet, hf, Matrix.toBlocks_fromBlocks₁₁]
    rfl
  refine ⟨?_, ?_⟩
  · rw [Avac.a_mul_par_k d ht h, hdetU, absE_adrU d.cm w τ]
  · obtain ⟨p, tp, hp, k, hk, rfl⟩ := d.ok.hgt.iwa h
    rw [d.ok.hgt.val p tp hp k hk]
    exact NNReal.coe_nonneg _
end PositivityTheory.SiegelWeilFormula.AStep
end

section
namespace PositivityTheory.SiegelWeilFormula.AStep
theorem cOneLaw_k (H : Hyps_k) {d : SD_k σ} (R : RD_k d) (L : LD_k d) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (w : InfinitePlace F)
    {nb' lam' 𝓖'} (_hc' : CoefData (Y := L.Y) L.b nb' lam' 𝓖') (T' : nF σ L.Y L.b)
    (τ : ℝ) (y : GR d.n) (hy : IsDil (Pi.single L.i₀ 1) τ y) (z : ℂ) (x : d.G) :
    cOne_k d L (d.sec0 Φ) d.s₀ z nb' lam' 𝓖' T' (R.ι w y * x) =
      exp (τ * (2 * z + d.n)) * cOne_k d L (d.sec0 Φ) d.s₀ z nb' lam' 𝓖' T' x := by
  set c := exp (τ * (2 * z + d.n)) with hc
  have hterm : ∀ g : L.sd.G, ((d.Ht (L.j g * (R.ι w y * x)) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * (R.ι w y *
      x)) =
      c * (((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g * x)) := by
    intro g
    rw [← mul_assoc, j_comm_dil_k R L w τ y hy g, mul_assoc]
    obtain ⟨ha, h0⟩ := a_dil_k R w L.i₀ τ y hy (L.j g * x)
    rw [constantTerm_dilation H R w L.i₀ τ y hy hΦ]
    have e1 : ((d.Ht (R.ι w y * (L.j g * x)) : ℝ) : ℂ) = ((Real.exp (2 * τ) : ℝ) : ℂ) * ((d.a (L.j g * x) : ℝ) : ℂ) :=
        by
      unfold SD_k.Ht
      rw [Real.coe_toNNReal _ (by rw [ha]; exact mul_nonneg (Real.exp_pos _).le h0), ha, Complex.ofReal_mul]
    have e2 : ((d.Ht (L.j g * x) : ℝ) : ℂ) = ((d.a (L.j g * x) : ℝ) : ℂ) := by
      unfold SD_k.Ht
      rw [Real.coe_toNNReal _ h0]
    rw [e1, e2, Complex.ofReal_mul_cpow (Real.exp_pos _).le, cpow_exp, hc]
    have e3 : exp (((2 * τ : ℝ) : ℂ) * (z - s0 d.m d.n)) * exp (τ * d.m) = exp (τ * (2 * z +
        d.n)) := by
      rw [← Complex.exp_add]
      congr 1
      unfold s0
      push_cast
      ring
    rw [← e3]
    ring
  unfold cOne_k
  have hfun := funext hterm
  rw [hfun]
  have hcs : ∀ (Ψ : L.sd.G → ℂ), cosetSum (par2 σ L.Y) (rat2 σ L.Y) (fun g => c * Ψ g) =
      fun g' => c * cosetSum (par2 σ L.Y) (rat2 σ L.Y) Ψ g' := by
    intro Ψ
    funext g'
    simp only [cosetSum, term]
    exact tsum_mul_left
  rw [hcs]
  simp only [fc, mul_assoc]
  exact integral_const_mul _ _
end PositivityTheory.SiegelWeilFormula.AStep
end
end

section
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
variable {σ : E →ₐ[F] E}
theorem isFrames_of'_k {d : SD_k σ} (R :
  RD_k d) (η : E) (hη : η ≠ 0) (hcm :
  HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ)
    (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) (hηζ : (σ η = η ∧ R.ζ = 1) ∨ (σ η = -η ∧ R.ζ = Complex.I))
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star
      (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star) :
    Gen.IsFrames (KWhit.Jd_k d η) θ
      (εsW_k R η) fr := by
  intro w
  set τ := (d.B.emb w).1 with hτ
  set a := τ η with ha
  set c := cW d.B η w with hc
  have hθ1 : ∀ x : E, θ w ((1 : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) ⊗ₜ[F] x) = star (τ x) := fun x => by
    have := th w ((1 : AF F) ⊗ₜ[F] x)
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, piInf_one] at this
    exact this
  have hmat : (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F)
    (KWhit.Jd_k d η)).map (θ w) = a • d.A.J.map τ := by
    ext i j
    simp only [Matrix.map_apply, HeckeCharacterZeroLocus.SiegelWeilU.JR,
      KWhit.Jd_k, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
      HeckeCharacterZeroLocus.SiegelWeilU.inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.includeRight_apply, hθ1]
    rw [← hcm.2.2.2, herm, map_mul]
  have hcs : star c = c := Complex.conj_ofReal _
  have hfrH : ((fr w).1)ᴴ = c • ((R.fr w).1)ᵀ := by
    rw [frc w, Matrix.conjTranspose_smul]
    change star c • _ = _
    rw [hcs]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hζ : R.ζ ≠ 0 := by
    rcases hηζ with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
  have hfr' : (R.fr w).1ᵀ * d.A.J.map τ * (R.fr w).1.map star = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by
    have := congrArg (fun M => R.ζ⁻¹ • M) (R.hfr w)
    simp only [smul_smul, inv_mul_cancel₀ hζ, one_smul] at this
    rw [this]
  have ha0 : a ≠ 0 := (map_ne_zero τ).2 hη
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hcc : c * c = ((‖a‖⁻¹ : ℝ) : ℂ) := by
    rw [hc, cW, ← Complex.ofReal_mul, ← Real.rpow_add hapos]
    norm_num [Real.rpow_neg_one]
  set z := a / R.ζ * ((R.sg w : ℤ) : ℂ) with hz
  have hsg : ‖((R.sg w : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or (R.sg w) with h | h <;> rw [h] <;> simp
  have hsg0 : ((R.sg w : ℤ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hsg; simp at hsg
  have hsgim : (((R.sg w : ℤ) : ℂ)).im = 0 := by simp
  have hz0 : z ≠ 0 := mul_ne_zero (div_ne_zero ha0 hζ) hsg0
  have hzn : ‖z‖ = ‖a‖ := by
    rw [hz, norm_mul, norm_div, hsg]
    rcases hηζ with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
  have hzim : z.im = 0 := by
    have hconj := hcm.2.2.2 τ η
    rcases hηζ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hconj
      have him : a.im = 0 := by
        have := congrArg Complex.im hconj
        change a.im = (star a).im at this
        simp at this; linarith
      rw [hz, h2, div_one, Complex.mul_im, him, hsgim]; ring
    · rw [h1, map_neg] at hconj
      have hre : a.re = 0 := by
        have := congrArg Complex.re hconj
        change (-a).re = (star a).re at this
        simp at this; linarith
      rw [hz, h2, Complex.div_I, Complex.mul_im, hsgim]
      simp [Complex.mul_im, hre]
  have key : (fr w).1ᴴ * (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F)
    (KWhit.Jd_k d η)).map (θ w) * (fr w).1 =
      (((‖z‖⁻¹ : ℝ) : ℂ) * z) • (1 : Matrix (Fin d.m) (Fin d.m) ℂ) := by
    rw [hfrH, hmat, frc w, show ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = c from rfl]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hfr', smul_smul, hzn, ← hcc, hz]
    congr 1
    field_simp
  change (fr w).1ᴴ * (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F)
    (KWhit.Jd_k d η)).map (θ w) * (fr w).1 = _
  rw [key, norm_inv_mul_self hz0 hzim]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [εsW_k, sgn, hz, ha, hτ]
  · simp [hij]
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end

section
open scoped ComplexOrder
open Matrix (fromBlocks transpose_apply)
namespace PositivityTheory.SiegelWeilFormula.KWhit
variable {σ : E →ₐ[F] E}
theorem rel_aniso_k (d : SD_k σ) (η : E) (hη : η ≠ 0) (y : Fin d.m → E)
    (hy : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd_k d η) y y = 0) : y = 0 := by
  by_contra hy0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (d.B.emb w).1
  have hτ : ∀ x, τ (σ x) = star (τ x) := d.ok.good.cm.2.2.2 τ
  let z : Fin d.m → ℂ := fun i => τ (y i)
  have hz : z ≠ 0 := by
    intro h
    apply hy0
    funext i
    apply τ.injective
    simpa [z] using congrFun h i
  have key : τ (HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd_k d η) y y) = τ η * (z ⬝ᵥ (d.A.J.map τ) *ᵥ star z) := by
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Jd_k, Matrix.mulVec,
      dotProduct, map_sum, map_mul,
    transpose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [z]
    rw [show ((σ : E →+* E) (y j)) = σ (y j) from rfl, hτ]
    ring
  rw [hy, map_zero] at key
  have hQ : z ⬝ᵥ (d.A.J.map τ) *ᵥ star z ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact rel_definite _ (hA.sig w) d.ok.aniso z hz
    · have h1 := rel_definite _ (hA.sig w) d.ok.aniso z hz
      intro h0
      apply h1
      simp only [Matrix.smul_mulVec, dotProduct_smul]
      change Complex.I • (z ⬝ᵥ d.A.J.map τ *ᵥ star z) = 0
      rw [h0, smul_zero]
  have hτη : τ η ≠ 0 := (map_ne_zero τ).mpr hη
  exact (mul_ne_zero hτη hQ) key.symm
theorem unipotentParam_rational_matrix (d : SD_k σ) (T : nF σ d.Y d.b) : ∃ T₀
  : Matrix (Fin d.n) (Fin d.n) E, T.1.1 = incM F T₀ := by
  obtain ⟨T, hT⟩ := T
  induction hT using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, by ext i j; simp [incM]⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    refine ⟨X + Y, ?_⟩
    change x.1 + y.1 = _
    rw [hX, hY]
    ext i j
    simp [incM]
  | neg x _ hx =>
    obtain ⟨X, hX⟩ := hx
    refine ⟨-X, ?_⟩
    change -x.1 = _
    rw [hX]
    ext i j
    simp [incM]
def relH_k (d : SD_k σ) (η : E) (β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin
  d.n) (AE F E) :=
  -(inclR (F := F) (E := E) (AF F) η⁻¹ • β.1ᵀ)
section
variable (d : SD_k σ)
theorem relH_mem_k (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (β : nA σ d.Y d.b) :
    relH_k d η β ∈ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n := by
  intro a b
  have hn := congrFun (congrFun (rel_nA_cond_k d ε hε β) a) b
  simp only [Matrix.add_apply, transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Matrix.zero_apply] at hn
  have he2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have hinv : σ η⁻¹ = -(((ε : ℤ) : E) * η⁻¹) := by
    rw [map_inv₀, hση, inv_neg, mul_inv, inv_eq_of_mul_eq_one_right he2]
  have hc : ∀ x : E,
    cA σ (inclR (AF F) x) =
    inclR (AF F) (σ x) := by
    intro x
    simp [cA, inclR, Algebra.TensorProduct.map_tmul]
  simp only [relH_k, Matrix.neg_apply, Matrix.smul_apply, transpose_apply, smul_eq_mul]
  rw [map_neg, map_mul, rel_sigR_eq_cA, rel_sigR_eq_cA, hc, hinv, map_neg, map_mul, map_intCast]
  linear_combination (inclR (AF F) η⁻¹) * hn
theorem relH_eq_k (η : E) (hη : η ≠ 0) (β : nA σ d.Y d.b) :
    β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * (relH_k d η β)ᵀ) := by
  have h1 : inclR (F := F) (E := E) (AF F) η *
    inclR (F := F) (AF F) η⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hη, map_one]
  ext i j
  simp [relH_k, incM, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, ← mul_assoc]
  rw [mul_comm (inclR (AF F) η⁻¹), h1,
    one_mul]
theorem rel_Td_k (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (T : nF σ d.Y d.b) (hT : IsND T) (T₀ : Matrix (Fin d.n) (Fin d.n) E)
    (h0 : T.1.1 = incM F T₀) : (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧ (Td η T₀).det ≠ 0 := by
  have hn := rel_nA_cond_k d ε hε T.1
  rw [h0, rel_cA_incM] at hn
  have hn' : incM F (T₀ᵀ + ((ε : ℤ) : E) • T₀.map σ) = incM F 0 := by
    have e0 : incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0 := by
      ext i j
      simp [incM]
    rw [e0, ← hn]
    ext i j
    simp [incM]
  have hz := rel_incM_injective hn'
  refine ⟨fun a b => ?_, ?_⟩
  · have he := congrFun (congrFun hz a) b
    simp only [Matrix.add_apply, transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Matrix.zero_apply] at he
    simp only [Td, transpose_apply, Matrix.smul_apply, smul_eq_mul]
    rw [map_mul, map_mul, map_neg, map_ofNat, hση]
    linear_combination (2 * η) * he
  · have hdet : T₀.det ≠ 0 := by
      intro h
      apply hT
      show (T.1.1).det = 0
      rw [h0, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
    simp only [Td, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hη)) hdet
end
theorem relAlg_pf_k : RelAlg_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨η, hη, hση, hherm⟩ := rel_eta_k d ε hε
  refine ⟨η, fun β => ⟨relH_k d η β, relH_mem_k d ε hε η hη hση β⟩, hη, hherm, fun β => relH_eq_k d η hη β,
    fun y hy => rel_aniso_k d η hη y hy, d.ok.good.cm, ⟨fun i j => ?_, ?_⟩, fun T hT => ?_⟩
  · simp only [Jd_k, transpose_apply, Matrix.smul_apply, smul_eq_mul]
    exact hherm j i
  · intro h0
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hy0
    apply rel_aniso_k d η hη y
    have h2 : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd_k d η) y y = ∑ i, σ (y i) * (Jd_k d η *ᵥ y) i := by
      simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Matrix.mulVec,
        dotProduct, Finset.mul_sum, mul_assoc]
      rfl
    rw [h2, hy]
    simp
  · obtain ⟨T₀, h0⟩ := unipotentParam_rational_matrix d T
    exact ⟨T₀, h0, rel_Td_k d ε hε η hη hση T hT T₀ h0⟩
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
