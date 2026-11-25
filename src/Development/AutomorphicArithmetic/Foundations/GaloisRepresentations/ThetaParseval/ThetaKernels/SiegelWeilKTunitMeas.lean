module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DoubledLagrangianContinuous
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfCells
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilOswgenFockOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.DZMulDZInv
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FiniteLineActions.GeoLine
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.ContinuousLoc
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.ExpAlg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.PolyGaussOfLines
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CBDM
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContSingle
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FrameDil
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.AlgInjective
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.IsOpAdm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.JjMulJj
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.SySmulRight
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.SymplecticFormCoordinates
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.ActUDiagMonomial
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.GIinvA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.GIinvCut
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsSigmaNe
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PiMapConst
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.WMUnitary
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitB
public import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
public import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactOfUnits
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import Mathlib.Analysis.Real.Pi.Irrational

/-! # SiegelWeilKTunitMeas: Consolidated global theta-kernel definitions and proofs (SiegelWeilKTunitMeas). -/
@[expose] public section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder SchwartzMap InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
open GlobalTheory.RatWeilOp PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Act
open GlobalTheory.Doubling (absE)
namespace CL
private theorem rEx_k (d : SD_k σ) (w : InfinitePlace F) : ∃ r : ℝ → GroundTheory.Global.IdeleGroup F,
    (∀ τ τ', r (τ + τ') = r τ * r τ') ∧ r 0 = 1 ∧
    (∀ τ, (GroundTheory.Global.IdeleGroup.ideleModule F (r τ) : ℝ) = Real.exp τ) ∧
    (∀ τ, piInf (d.B.emb w) ((r τ : AF F) • (1 : AE F E)) = (Real.exp τ : ℂ)) ∧
    (∀ τ w', w' ≠ w → piInf (d.B.emb w') ((r τ : AF F) • (1 : AE F E)) = 1) ∧
    (∀ τ, finOne F * (r τ : AF F) = finOne F) := by
  have := d.cm.1; have hw : w.IsReal := IsTotallyReal.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let u : ℝ → ℝˣ := fun τ => ⟨Real.exp τ, Real.exp (-τ), by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero],
    by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]⟩
  let r : ℝ → GroundTheory.Global.IdeleGroup F :=
    fun τ => GroundTheory.Global.IdeleGroup.infiniteEmbedding w (Units.map e.symm.toMonoidHom (u τ))
  have hee : ∀ x : ℝ, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (e.symm x) = x := e.apply_symm_apply
  refine ⟨r, fun τ τ' => by simp only [r, show u (τ + τ') = u τ * u τ' from Units.ext (Real.exp_add τ τ'), map_mul],
    by simp only [r, show u 0 = 1 from Units.ext Real.exp_zero, map_one], fun τ => ?_, fun τ => ?_,
    fun τ w' hw' => ?_, fun τ => Prod.ext (by change (0 : Ainf F) * _ = 0; rw [zero_mul])
      (by change (1 : Af F) * (1 : Af F) = 1; rw [mul_one])⟩
  · rw [GroundTheory.Global.IdeleGroup.ideleModule_infiniteEmbedding, hw.mult_eq_one, pow_one]
    show ‖e.symm (Real.exp τ)‖ = _
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), hee,
      Real.norm_of_nonneg (Real.exp_pos τ).le]
  · rw [St.piInf_smul, map_one, mul_one, show ((r τ : AF F)).1 =
      GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (e.symm (Real.exp τ)) from rfl,
      GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply, Pi.mulSingle_eq_same,
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, hee]
  · rw [St.piInf_smul, map_one, mul_one, show ((r τ : AF F)).1 =
      GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (e.symm (Real.exp τ)) from rfl,
      GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hw', map_one]
private theorem frame_dil_k (d : SD_k σ) (R : RD_k d) (w : InfinitePlace F) (r : ℝ → GroundTheory.Global.IdeleGroup F)
    (hw : ∀ τ, piInf (d.B.emb w) ((r τ : AF F) • (1 : AE F E)) = (Real.exp τ : ℂ))
    (ho : ∀ τ w', w' ≠ w → piInf (d.B.emb w') ((r τ : AF F) • (1 : AE F E)) = 1)
    (hf : ∀ τ, finOne F * (r τ : AF F) = finOne F) (i₀ : Fin d.n) {τ : ℝ} {y : GR d.n}
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    inFrame d.b (R.ι w y) = dM i₀ ((r τ : AF F) • (1 : AE F E)) ((r (-τ) : AF F) • (1 : AE F E)) := by
  have hC : Matrix.fromBlocks (Matrix.diagonal fun j => (Real.exp (τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j) : ℂ)) 0 0
      (Matrix.diagonal fun j => (Real.exp (-(τ * (Pi.single i₀ 1 : Fin d.n → ℝ) j)) : ℂ)) =
      dM i₀ (Real.exp τ : ℂ) (Real.exp (-τ) : ℂ) := by
    ext (u | u) (v | v) <;>
      simp only [dM_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_false,
        Matrix.zero_apply] <;>
      (rcases eq_or_ne u v with rfl | h
       · by_cases h' : u = i₀ <;> simp [h']
       · simp [h])
  refine Place.cw_ext_k d (fun w' => ?_) ?_
  · by_cases hw' : w' = w
    · subst hw'; rw [R.cw_iota_pf w' y, hy, dZ_conj_diag (Krd.zeta_ne R.hζ), hC, SD_k.cw, dM_map, hw, hw]
    · rw [R.off_w w w' y hw', SD_k.cw, dM_map, ho τ w' hw', ho (-τ) w' hw']
      ext u v; rw [dM_apply, Matrix.one_apply]; split_ifs <;> rfl
  · rw [R.off_f w y]; ext u v; rw [Matrix.smul_apply, Matrix.smul_apply, dM_apply, Matrix.one_apply]
    have e : ∀ t, finOne F • ((r t : AF F) • (1 : AE F E)) = finOne F • (1 : AE F E) := fun t => by rw [smul_smul, hf]
    split_ifs <;> simp [e]
end CL
theorem secUnf_of_k : AbsConv_k → SecUnf_k := by
  intro hA F E _ _ _ _ _ σ d R L s₁ f hf he
  obtain ⟨t, ht⟩ := hA F E σ d L s₁ f hf he
  refine ⟨t, fun z hz nb lam 𝓖 hc hk uM ν 𝓤 hU hkU T T' hT nb' lam' 𝓖' hc' hk' => ?_⟩
  have hε := R.hε
  have hem : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
  set e : AE F E := ((R.ε : ℤ) : AE F E)
  have hee : e * e = 1 := by rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  obtain ⟨δ, hδ0, hδ⟩ := CL.deltaEx' d.cm R.ε
  obtain ⟨κ, hκ, hsc⟩ := CL.measEx' (F := F) (E := E) L.n d.bs
  let M₀ : Matrix d.N2 d.N2 E := CL.wM L.i₀ (1 : E) ((R.ε : ℤ) : E)
  let M₀' : Matrix d.N2 d.N2 E := CL.wM L.i₀ ((R.ε : ℤ) : E) (1 : E)
  have hW : incM F M₀ = CL.wM L.i₀ (1 : AE F E) e := by show M₀.map _ = _; rw [CL.wM_map, map_one, map_intCast]
  have hW' : incM F M₀' = CL.wM L.i₀ e (1 : AE F E) := by show M₀'.map _ = _; rw [CL.wM_map, map_one, map_intCast]
  obtain ⟨w₁, hw₁⟩ := kunf.exists_of_frame hε (incM F M₀) (incM F M₀')
    (by rw [hW, hW']; exact CL.wM_mul L.i₀ _ _ _ _ (one_mul 1) hee)
    (by
      rw [hW]
      exact CL.wM_unitary L.i₀ (cA σ).toRingHom 1 e e (by simp only [AlgHom.toRingHom_eq_coe, map_one, mul_one, hee])
        (by simp only [AlgHom.toRingHom_eq_coe, e, map_intCast, one_mul]))
  have hw₁' : inFrame d.b w₁ = CL.wM L.i₀ (1 : AE F E) e := hw₁.trans hW
  set δ' : AE F E := inclR (F := F) (AF F) δ with hδ'
  let Mc : (Fin L.n → AE F E) × AF F → Matrix d.N2 d.N2 (AE F E) :=
    fun c => CL.cB L.i₀ L.em c.1 (fun j => cA σ (c.1 j)) (c.2 • δ')
  let Mc' : (Fin L.n → AE F E) × AF F → Matrix d.N2 d.N2 (AE F E) :=
    fun c => CL.cB L.i₀ L.em (-c.1) (-fun j => cA σ (c.1 j)) (-(c.2 • δ'))
  have hcont : ∀ s : AF F → AF F, Continuous s → ∀ q : (Fin L.n → AE F E) → (Fin L.n → AE F E), Continuous q →
      Continuous fun c : (Fin L.n → AE F E) × AF F => CL.cB L.i₀ L.em (q c.1) (fun j => cA σ (q c.1 j)) (s c.2 • δ') :=
    fun s hs q hq => Continuous.matrix_fromBlocks
      (continuous_const.add (continuous_finsetSum _ fun j _ =>
        cont_single _ _ ((continuous_apply j).comp (hq.comp continuous_fst))))
      (cont_single _ _ (Continuous.smul (f := fun c : (Fin L.n → AE F E) × AF F => s c.2) (g := fun _ => δ')
        (hs.comp continuous_snd) continuous_const)) continuous_const
      (continuous_const.sub (continuous_finsetSum _ fun j _ => cont_single _ _
        ((GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ).comp
          ((continuous_apply j).comp (hq.comp continuous_fst)))))
  have hMc : Continuous Mc := hcont id continuous_id id continuous_id
  have hMc' : Continuous Mc' := by
    convert hcont (fun a => -a) continuous_neg (fun u => -u) continuous_neg using 2 with c
    simp only [Mc', neg_smul, Pi.neg_apply, map_neg]; rfl
  have hcA_z : ∀ a : AF F, cA σ (a • δ') = -(e * (a • δ')) := fun a => by
    rw [map_smul, hδ', show cA σ (inclR (F := F) (AF F) δ) = inclR (F := F) (AF F) (σ δ) by
      show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] σ δ
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply],
      hδ, map_neg, map_mul, map_intCast, smul_neg, mul_smul_comm]
  set B0 := incM F d.b.1; set Bi := incM F (d.b⁻¹).1
  have e1 : B0 * Bi = 1 := GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv d.b
  have e2 : Bi * B0 = 1 := GlobalTheory.EisBL.DoubledParabolic.incM_inv_mul d.b
  let U : (Fin L.n → AE F E) × AF F → GL d.N2 (AE F E) := fun c =>
    ⟨B0 * Mc c * Bi, B0 * Mc' c * Bi,
      by calc B0 * Mc c * Bi * (B0 * Mc' c * Bi)
            = B0 * (Mc c * (Bi * B0) * Mc' c) * Bi := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [e2, Matrix.mul_one, CL.cB_mul hem c.1 _ _, Matrix.mul_one, e1],
      by calc B0 * Mc' c * Bi * (B0 * Mc c * Bi)
            = B0 * (Mc' c * (Bi * B0) * Mc c) * Bi := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [e2, Matrix.mul_one, mul_eq_one_comm.1 (CL.cB_mul hem c.1 _ _), Matrix.mul_one, e1]⟩
  have hUmem : ∀ c, U c ∈ UG (cA σ) (dbl (incM F d.Y.J)) := fun c => by
    obtain ⟨x, hx⟩ := kunf.exists_of_frame (Y := d.Y) hε (Mc c) (Mc' c) (CL.cB_mul hem c.1 _ _)
      (CL.cB_unitary hem (cA σ).toRingHom (C5.cc_k d) e hee c.1 (c.2 • δ') (hcA_z c.2))
    have hx1 : x.1 = U c := Units.ext (by
      show mat2 x = B0 * Mc c * Bi; rw [← hx]
      calc mat2 x = (B0 * Bi) * mat2 x * (B0 * Bi) := by rw [e1, Matrix.one_mul, Matrix.mul_one]
        _ = B0 * (Bi * mat2 x * B0) * Bi := by simp only [Matrix.mul_assoc])
    exact hx1 ▸ x.2
  let cM : (Fin L.n → AE F E) × AF F → d.G := fun c => ⟨U c, hUmem c⟩
  have hcMc : Continuous cM := continuous_induced_rng.2 (Units.continuous_iff.2
    ⟨(continuous_const.matrix_mul hMc).matrix_mul continuous_const,
     (continuous_const.matrix_mul hMc').matrix_mul continuous_const⟩)
  have hcM : ∀ c, inFrame d.b (cM c) = Mc c := fun c => by
    show Bi * (B0 * Mc c * Bi) * B0 = Mc c
    calc Bi * (B0 * Mc c * Bi) * B0 = (Bi * B0) * Mc c * (Bi * B0) := by simp only [Matrix.mul_assoc]
      _ = Mc c := by rw [e2, Matrix.one_mul, Matrix.mul_one]
  have hfr := fun x y => GlobalTheory.EisBL.DoubledParabolic.inFrame_mul (σ := σ) (Y := d.Y) d.b x y
  have hlaw : CLaw_k R L w₁ cM κ := ⟨
    fun w τ y g hy => by
      obtain ⟨r, -, -, -, hrw, hro, hrf⟩ := CL.rEx_k d w
      apply kunf.inFrame_injective d.b
      rw [hfr, hfr, CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy]; exact CL.comm_dM L.i₀ _ (L.j_out g) _ _,
    fun w τ y hy => by
      obtain ⟨r, -, -, -, hrw, hro, hrf⟩ := CL.rEx_k d w
      have hy' := CL.isDil_inv hy; obtain ⟨t0, ht0⟩ := d.ok.frame.2
      set A : Matrix (Fin d.n) (Fin d.n) ℂ :=
        Matrix.diagonal fun j => (Real.exp (-τ * (Pi.single L.i₀ 1 : Fin d.n → ℝ) j) : ℂ)
      set D : Matrix (Fin d.n) (Fin d.n) ℂ :=
        Matrix.diagonal fun j => (Real.exp (-(-τ * (Pi.single L.i₀ 1 : Fin d.n → ℝ) j)) : ℂ)
      obtain ⟨-, hA', -, hoA, hfA, -⟩ := R.frame_diag w y⁻¹ A D hy'
      obtain ⟨t', ht', habs⟩ := KSplitP.iota_isPar_k d R w y⁻¹ (by rw [hy', Matrix.toBlocks_fromBlocks₂₁])
      have hdetA : A.det = (Real.exp (-τ) : ℂ) := by
        rw [Matrix.det_diagonal, Finset.prod_eq_single L.i₀ (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
          (fun h => absurd (Finset.mem_univ _) h)]; simp
      have ha : (absE F E (Matrix.GeneralLinearGroup.det t') : ℝ) = Real.exp (-(2 * τ)) := by
        rw [habs, hy', Matrix.toBlocks_fromBlocks₁₁, hdetA, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos (-τ)).le, ← Real.exp_natCast_mul]; congr 1; push_cast; ring
      have hχ : (d.χ (Matrix.GeneralLinearGroup.det t') : ℂ) = 1 := by
        have ht1 := ((kunf.isPar_frame ht0 (R.ι w y⁻¹) t').1 ht').2
        have hcw : ∀ w', d.cw w' t'.1 = d.cw w' (incM F t0.1) * d.cw w' (inFrame d.b (R.ι w y⁻¹)).toBlocks₁₁ *
            d.cw w' (incM F (t0⁻¹).1) := fun w' => by rw [ht1]; simp only [SD_k.cw, Matrix.map_mul]
        have hI : incM F t0.1 * incM F (t0⁻¹).1 = 1 := by
          rw [← kunf.incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]
        have hT' : ∀ w', d.cw w' (incM F t0.1) * d.cw w' (incM F (t0⁻¹).1) = 1 := fun w' => by
          rw [SD_k.cw, SD_k.cw, ← Matrix.map_mul, hI, Matrix.map_one _ (map_zero _) (map_one _)]
        have hdet : (d.cw w t'.1).det = (Real.exp (-τ) : ℂ) := by
          have hXY := congrArg Matrix.det (hT' w); rw [Matrix.det_mul, Matrix.det_one] at hXY
          rw [hcw, Matrix.det_mul, Matrix.det_mul, hA', hdetA]; linear_combination ((Real.exp (-τ) : ℝ) : ℂ) * hXY
        rw [RD_k.chi_det (d := d) w t' _ rfl (fun w' h => by rw [hcw, (hoA w' h).1, Matrix.mul_one, hT'])
          (by rw [ht1, ← Matrix.smul_mul, ← Matrix.mul_smul, hfA, Matrix.mul_smul, Matrix.smul_mul,
            Matrix.mul_one, hI]), hdet]
        exact d.chiW_pos w _ (Real.exp_pos (-τ))
      refine ⟨R.ι w y⁻¹, t', ht', ha, hχ, ?_⟩
      apply kunf.inFrame_injective d.b
      rw [hfr, hfr, hw₁', CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy, CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy',
        neg_neg]
      exact CL.wM_dM L.i₀ _ _ _ _,
    fun w τ y hy => by
      obtain ⟨r, hr0, hr1, hrm, hrw, hro, hrf⟩ := CL.rEx_k d w
      obtain ⟨sc, hsc1, hsc2⟩ := hsc (r (-τ))
      refine ⟨sc, fun c => ?_, ?_⟩
      · apply kunf.inFrame_injective d.b
        rw [hfr, hfr, hcM, hcM, CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy]
        have hxy : ((r τ : AF F) • (1 : AE F E)) * ((r (-τ) : AF F) • (1 : AE F E)) = 1 := by
          rw [smul_mul_smul_comm, one_mul, ← Units.val_mul, ← hr0, add_neg_cancel, hr1]; simp
        rw [CL.cB_dM hem _ _ _ _ _ hxy, hsc1]; congr 1; simp only [Mc]; congr 1
        · funext j; exact smul_one_mul _ _
        · funext j; rw [map_smul, smul_one_mul]
        · rw [mul_assoc, smul_one_mul, smul_one_mul, smul_assoc, mul_smul]
      · rw [hsc2, hrm, ← Real.exp_neg, neg_neg, ← Real.exp_natCast_mul, ← Atop.LD.n_succ_k L]
        congr 3; push_cast; ring⟩
  have h : C5.Hyp_k L nb uM nb' w₁ cM δ :=
    { nb := hc.1, uM := hU.1, nb' := hc'.1, wr := kunf.rat_of_inFrame hw₁,
      wf := ⟨1, (R.ε : ℤ), one_ne_zero, by simp, by rw [hw₁']; simp [CL.wM, map_intCast, map_one, e]⟩,
      cf := fun c => ⟨_, hcM c⟩, δ0 := hδ0 }
  obtain ⟨K, hK⟩ := C5.unf_k R hf z hc hU hT hc' (fun x => ht z hz nb lam 𝓖 hc hk uM ν 𝓤 hU hkU T x) h hcMc hκ
  exact ⟨w₁, cM, κ, hlaw, K, hK⟩
end Act
section
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
namespace TBij_k
open TBij TBij.Adp
namespace Adp
variable (d : SD_k σ)
abbrev sy : d.M2 → d.M2 → AF F := symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))
abbrev yy : Matrix d.N2 (Fin d.n) (AE F E) := incM F d.b.1.toCols₂
abbrev dg : Matrix d.N2 (Fin d.n) (AE F E) := diagCols (Fin d.n)
abbrev Ix : Type := d.I3
def xs (w : d.M2) : d.MxE := (w * (incM F (d.b⁻¹ : GL d.N2 E).1)ᵀ).toCols₂
theorem sy_eq (w w' : d.M2) : sy d w w' = om (d.dd.e w) (d.dd.e w') := d.dd.form w w'
private theorem sy_add_l (w₁ w₂ w' : d.M2) : sy d (w₁ + w₂) w' = sy d w₁ w' + sy d w₂ w' := by
  simp only [sy_eq, map_add (f := _), om, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring
theorem sy_add_r (w w₁ w₂ : d.M2) : sy d w (w₁ + w₂) = sy d w w₁ + sy d w w₂ := by
  simp only [sy_eq, map_add (f := _), om, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring
theorem sy_smul_r (a : AF F) (w w' : d.M2) : sy d w (a • w') = a * sy d w w' := by
  simp only [sy_eq, map_smul, om, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring
private theorem sy_frame (X X' : d.MxE) : sy d (X * (yy d)ᵀ) (X' * (yy d)ᵀ) = 0 := by
  have hf : (d.b.1.toCols₂)ᵀ * dbl d.Y.J * d.b.1.toCols₂.map σ = 0 := by
    obtain ⟨ε, h⟩ := d.ok.frame.1; have h2 := congrArg Matrix.toBlocks₂₂ h
    rw [Matrix.toBlocks_fromBlocks₂₂] at h2
    rw [← h2]; ext i j; simp [Matrix.toBlocks₂₂, Matrix.mul_apply, Matrix.toCols₂]
  have h : (yy d)ᵀ * dbl (incM F d.Y.J) * (yy d).map (cA σ) = 0 := by
    rw [yy, cA_incM, ← incM_dbl, ← incM_transpose, ← TBij.incM_mul, ← TBij.incM_mul, hf, incM_zero']
  simp only [sy, symp]; rw [hTens_outer _ _ _ _ _ _ _ h, mul_zero, map_zero]
theorem decomp (w : d.M2) : ∃ Z : d.MxE, w = Z * (dg d)ᵀ + xs d w * (yy d)ᵀ := by
  obtain ⟨t, ht⟩ := d.ok.frame.2
  set V := w * (incM F (d.b⁻¹ : GL d.N2 E).1)ᵀ
  have h1 : w = V * (incM F d.b.1)ᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← TBij.incM_mul, Units.mul_inv, incM_one', Matrix.transpose_one,
      Matrix.mul_one]
  have h2 : incM F d.b.1 = Matrix.fromCols (incM F d.b.1.toCols₁) (incM F d.b.1.toCols₂) := by ext i (j | j) <;> rfl
  refine ⟨V.toCols₁ * (incM F t.1)ᵀ, ?_⟩
  change w = _ + V.toCols₂ * _
  conv_lhs => rw [h1, h2, ← Matrix.fromCols_toCols V]
  have ht' : incM F d.b.1.toCols₁ = @HMul.hMul (Matrix d.N2 (Fin d.n) (AE F E)) d.Mn (Matrix d.N2 (Fin d.n) (AE F E))
      Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (diagCols (Fin d.n)) (incM F t.1) := by
    rw [ht, ← incM_diagCols (F := F) (E := E)]; exact TBij.incM_mul _ _
  rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, ht', Matrix.transpose_mul, ← Matrix.mul_assoc]
private theorem xs_frame (X : d.MxE) : xs d (X * (yy d)ᵀ) = X := by
  have h1 : incM F (d.b⁻¹ : GL d.N2 E).1 * yy d = (1 : Matrix d.N2 d.N2 (AE F E)).toCols₂ := by
    have : (d.b⁻¹ : GL d.N2 E).1 * d.b.1.toCols₂ = (1 : Matrix d.N2 d.N2 E).toCols₂ := by
      rw [← Units.inv_mul d.b]; ext i j; simp [Matrix.mul_apply, Matrix.toCols₂]
    rw [yy, ← TBij.incM_mul, this]; ext i j; simp [incM, Matrix.toCols₂, Matrix.one_apply]
  rw [xs, Matrix.mul_assoc, ← Matrix.transpose_mul, h1]
  ext i j; simp [Matrix.toCols₂, Matrix.mul_apply, Matrix.one_apply]
theorem cmb_crd (X : d.MxE) : d.cmb (d.crd X) = X := KFock.cmb_crd_k d X
theorem crd_cmb (c : Ix d → AF F) : d.crd (d.cmb c) = c := KFock.crd_cmb_k d c
theorem crd_add (X X' : d.MxE) : d.crd (X + X') = d.crd X + d.crd X' := funext fun _ => by simp [SD_k.crd]
theorem crd_smul (a : AF F) (X : d.MxE) : d.crd (a • X) = a • d.crd X := funext fun _ => by simp [SD_k.crd]
private def cmbL : (Ix d → AF F) →ₗ[AF F] d.MxE where
  toFun := d.cmb
  map_add' _ _ := by ext i j; simp [SD_k.cmb, TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' _ _ := by ext i j; simp [SD_k.cmb, TensorProduct.smul_tmul']
def ek (k : Ix d) : d.MxE := d.cmb fun j => if k = j then 1 else 0
theorem cmb_sum (c : Ix d → AF F) : d.cmb c = ∑ k, c k • ek d k := LinearMap.pi_apply_eq_sum_univ (cmbL d) c
theorem crd_incM (M : d.ME) (k : Ix d) : d.crd (incM F M) k = algebraMap F (AF F) (d.bs.repr (M k.1 k.2.1) k.2.2) := by
  simp only [SD_k.crd, incM, Matrix.map_apply]
  rw [show inclR (F := F) (AF F) (M k.1 k.2.1) = (1 : AF F) ⊗ₜ[F] M k.1 k.2.1 from rfl,
    Algebra.TensorProduct.basis_repr_tmul]; simp
def c0 {κ : Type} [Fintype κ] (τ : κ ≃ Ix d) : d.M2 →ₗ[AF F] (κ → AF F) × (κ → AF F) where
  toFun w := (fun k => d.crd (xs d w) (τ k), fun k => sy d (ek d (τ k) * (yy d)ᵀ) w)
  map_add' w w' := Prod.ext (funext fun k => by
    have h : xs d (w + w') = xs d w + xs d w' := by ext i j; simp [xs, Matrix.add_mul, Matrix.toCols₂]
    simp [h, crd_add]) (funext fun k => sy_add_r d _ w w')
  map_smul' a w := Prod.ext (funext fun k => by
    have h : xs d (a • w) = a • xs d w := by ext i j; simp [xs, Matrix.smul_mul, Matrix.toCols₂]
    simp [h, crd_smul]) (funext fun k => sy_smul_r d a _ w)
theorem symplecticForm_coordinates {κ : Type} [Fintype κ] (τ : κ ≃ Ix d) (w w' : d.M2) :
    om (c0 d τ w) (c0 d τ w') = sy d w w' := by
  have hdot : ∀ (X : d.MxE) (u : d.M2),
      (fun k => d.crd X (τ k)) ⬝ᵥ (fun k => sy d (ek d (τ k) * (yy d)ᵀ) u) = sy d (X * (yy d)ᵀ) u := fun X u => by
    have hsum : ∀ (v : Ix d → d.M2), sy d (∑ i, d.crd X i • v i) u = ∑ i, d.crd X i * sy d (v i) u := fun v => by
      simp only [sy_eq, map_sum, map_smul, om, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
        sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [dotProduct, Equiv.sum_comp τ (fun i => d.crd X i * sy d (ek d i * (yy d)ᵀ) u), ← hsum]
    congr 1; conv_rhs => rw [← cmb_crd d X, cmb_sum, Matrix.sum_mul]
    simp only [Matrix.smul_mul]
  change (fun k => d.crd (xs d w) (τ k)) ⬝ᵥ (fun k => sy d (ek d (τ k) * (yy d)ᵀ) w') -
      (fun k => d.crd (xs d w') (τ k)) ⬝ᵥ (fun k => sy d (ek d (τ k) * (yy d)ᵀ) w) = sy d w w'
  rw [hdot, hdot]; obtain ⟨Z, hZ⟩ := decomp d w; obtain ⟨Z', hZ'⟩ := decomp d w'
  have hdiag : sy d (Z * (dg d)ᵀ) (Z' * (dg d)ᵀ) = 0 := by
    simp only [sy, symp]; rw [hTens_outer _ _ _ _ _ _ _ (isLagr_diagCols (cA σ) (incM F d.Y.J)).1, mul_zero, map_zero]
  have hanti : sy d (Z * (dg d)ᵀ) (xs d w' * (yy d)ᵀ) = -sy d (xs d w' * (yy d)ᵀ) (Z * (dg d)ᵀ) := by
    simp only [sy_eq, om]; ring
  have a1 : sy d w w' = sy d (Z * (dg d)ᵀ) w' + sy d (xs d w * (yy d)ᵀ) w' := by conv_lhs => rw [hZ]; rw [sy_add_l]
  have a2 : sy d (Z * (dg d)ᵀ) w' = sy d (Z * (dg d)ᵀ) (xs d w' * (yy d)ᵀ) := by
    conv_lhs => rw [hZ']; rw [sy_add_r, hdiag, zero_add]
  have a3 : sy d (xs d w' * (yy d)ᵀ) w = sy d (xs d w' * (yy d)ᵀ) (Z * (dg d)ᵀ) := by
    conv_lhs => rw [hZ]; rw [sy_add_r, sy_frame, add_zero]
  rw [a1, a2, a3, hanti]; ring
theorem coordinates_frame {κ : Type} [Fintype κ] (τ : κ ≃ Ix d) (X : d.MxE) :
    c0 d τ (X * (yy d)ᵀ) = (fun k => d.crd X (τ k), 0) :=
  Prod.ext (by change (fun k => d.crd (xs d (X * (yy d)ᵀ)) (τ k)) = _; rw [xs_frame]) (funext fun _ => sy_frame d _ _)
theorem coordinates_fst_eq_zero {κ : Type} [Fintype κ] (τ : κ ≃ Ix d) (w : d.M2) (h : (c0 d τ w).1 = 0) :
    ∃ Z : d.MxE, w = Z * (dg d)ᵀ := by
  have h1 : d.crd (xs d w) = 0 := funext fun i => by simpa [c0] using congrFun h (τ.symm i)
  have h2 : xs d w = 0 := by rw [← cmb_crd d (xs d w), h1]; exact (cmbL d).map_zero
  obtain ⟨Z, hZ⟩ := decomp d w; exact ⟨Z, by rw [hZ, h2, Matrix.zero_mul, add_zero]⟩
theorem coordinates_rational {κ : Type} [Fintype κ] (τ : κ ≃ Ix d) (x : Matrix (Fin d.m) d.N2 E) :
    ∃ y z : κ → F, c0 d τ (incM F x) = ratV y z := by
  have hs : ∀ k, ∃ r : F, sy d (ek d (τ k) * (yy d)ᵀ) (incM F x) = algebraMap F (AF F) r := fun k => by
    obtain ⟨M, hM⟩ : ∃ M : d.ME, ek d (τ k) = incM F M :=
      ⟨Matrix.of fun i j => ∑ k', (if τ k = (i, j, k') then (1 : F) else 0) • d.bs k', by
        ext i j; simp only [ek, SD_k.cmb, incM, Matrix.map_apply, Matrix.of_apply, map_sum]
        refine Finset.sum_congr rfl fun k' _ => ?_; show _ = (1 : AF F) ⊗ₜ[F] _; split_ifs <;> simp⟩
    rw [hM, yy, ← incM_transpose, ← TBij.incM_mul, sy_eq]
    obtain ⟨y, z, h⟩ := d.ok.dbl.rat (M * (d.b.1.toCols₂)ᵀ); obtain ⟨y', z', h'⟩ := d.ok.dbl.rat x
    exact ⟨om (y, z) (y', z'), by rw [h, h']; exact om_ratV y z y' z'⟩
  choose r hr using hs
  refine ⟨fun k => d.bs.repr (((x * ((d.b⁻¹ : GL d.N2 E).1)ᵀ).toCols₂) (τ k).1 (τ k).2.1) (τ k).2.2,
    r, Prod.ext (funext fun k => ?_) (funext hr)⟩
  change d.crd (xs d (incM F x)) (τ k) = _
  rw [show xs d (incM F x) = incM F ((x * ((d.b⁻¹ : GL d.N2 E).1)ᵀ).toCols₂) by
    rw [xs, ← incM_transpose, ← TBij.incM_mul]; rfl]
  exact crd_incM d _ (τ k)
theorem card_ix : Fintype.card d.κ = Fintype.card (Ix d) := by
  rw [card_eq d.bs d.dd.e, Fintype.card_prod, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_fin]; ring
theorem core : ∃ (τ : d.κ ≃ Ix d) (e : ((d.κ → AF F) → ℂ) →ₗ[ℂ] d.Fn) (C : ℂ), C ≠ 0 ∧
    Set.BijOn e (schA F d.κ : Set _) (schA F d.κ : Set _) ∧
    (∀ l ∈ (adeleClass F).adm d.κ, l ∘ₗ e ∈ (adeleClass F).adm d.κ) ∧
    ∀ Ψ ∈ schA F d.κ, ∀ X, d.T (e Ψ) X = C * Ψ (fun k => d.crd X (τ k)) := by
  classical
  have hψ : IsStd d.B.ψ := d.ok.good.std; have hD := d.ok.dbl
  let τ : d.κ ≃ Ix d := Fintype.equivOfCardEq (card_ix d)
  obtain ⟨a, ha, hact⟩ := exists_symp d.dd.e (c0 d τ) (fun w w' => by rw [symplecticForm_coordinates, sy_eq]) (by
    rintro w ⟨y, z, h⟩; obtain ⟨x, hx⟩ := rat_surj d.bs d.dd.e (fun x => hD.rat x) y z
    obtain rfl : w = incM F x := d.dd.e.injective (h.trans hx.symm); exact coordinates_rational d τ x)
  set J := jj d.κ F; set b := -(J * aᵀ * J)
  have hba : b * a = 1 := by
    rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc aᵀ, ha, jj_mul_jj, neg_neg]
  have hab : a * b = 1 := mul_eq_one_comm.1 hba
  have hbs : bᵀ * J * b = J := by
    calc bᵀ * J * b = bᵀ * (aᵀ * J * a) * b := by rw [ha]
      _ = (a * b)ᵀ * J * (a * b) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = J := by rw [hab, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨e, c, ei, ev, h⟩ := hasOp_of_symplectic d.ok.good.cm.1 hψ b hbs
  have hinv : ∀ w, act (b.map (algebraMap F (AF F))) (c0 d τ w) = d.dd.e w := fun w => by
    rw [hact w, ← act_mul, ← Matrix.map_mul, hba, Matrix.map_one _ (map_zero _) (map_one _), act_one']
  have hheis : ∀ w, ∀ Ψ ∈ schA F d.κ, e (schr d.B.ψ (c0 d τ w) Ψ) = d.dd.rho d.B.ψ w (e Ψ) := fun w Ψ hΨ => by
    rw [h.Heisenberg₂ _ Ψ hΨ, hinv]; rfl
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.CharInvForm.main F d.B.ψ hψ d.κ (d.l ∘ₗ e)
    (isOp_adm h d.l hD.adm) fun y φ hφ => by
      let w := d.dd.e.symm (act (b.map (algebraMap F (AF F))) (0, y))
      have hw : c0 d τ w = (0, y) := by
        rw [hact, LinearEquiv.apply_symm_apply, ← act_mul, ← Matrix.map_mul, hab,
          Matrix.map_one _ (map_zero _) (map_one _), act_one']
      obtain ⟨Z, hZw⟩ := coordinates_fst_eq_zero d τ w (by rw [hw])
      have e1 : (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = schr d.B.ψ (c0 d τ (Z * (dg d)ᵀ)) φ := by
        rw [← hZw, hw]; funext x; simp [schr]
      rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, hheis _ φ hφ]; exact hD.kill Z _ (h.maps φ hφ)
  have hT : ∀ Ψ ∈ schA F d.κ, ∀ X, d.T (e Ψ) X = C * Ψ (fun k => d.crd X (τ k)) := fun Ψ hΨ X => by
    have h1 := hC _ (GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ (c0 d τ (X * (yy d)ᵀ)) Ψ hΨ)
    rw [LinearMap.comp_apply, hheis _ Ψ hΨ, coordinates_frame] at h1; rw [SD_k.T, h1]; simp [schr]
  refine ⟨τ, e, C, fun hC0 => ?_, h.bijOn hψ, fun l hl => isOp_adm h l hl, hT⟩
  obtain ⟨Φ, hΦ, hθ⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F d.κ
  obtain ⟨Ψ, hΨ, rfl⟩ := (h.bijOn hψ).surjOn hΦ
  have h0 : ∀ y : d.ME, d.l (d.dd.rho d.B.ψ (incM F (Matrix.fromCols y (-y))) (e Ψ)) = 0 := fun y => by
    rw [← hheis _ Ψ hΨ]
    have := hC _ (GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ (c0 d τ (incM F (Matrix.fromCols y (-y)))) Ψ hΨ)
    rw [LinearMap.comp_apply] at this; rw [this, hC0, zero_mul]
  have h2 := hD.theta (e Ψ) hΦ; simp only [h0] at h2; exact hθ (h2.unique hasSum_zero)
end Adp
theorem tBij : TBij_k := by
  intro F E _ _ _ _ _ σ d; obtain ⟨τ, e, C, hC, hbij, -, hT⟩ := Adp.core d
  refine ⟨fun Φ hΦ => ?_, fun f hf => ?_, fun Φ hΦ h0 => ?_⟩
  · obtain ⟨Ψ, hΨ, rfl⟩ := hbij.surjOn hΦ; show (fun c => d.T (e Ψ) (d.cmb c)) ∈ schA F (Adp.Ix d)
    rw [show (fun c => d.T (e Ψ) (d.cmb c)) = C • fun x : Adp.Ix d → AF F => Ψ (x ∘ τ) from
      funext fun c => by rw [hT Ψ hΨ, Adp.crd_cmb]; rfl]
    exact Submodule.smul_mem _ C (comp_schA τ hΨ)
  · have hΨ : C⁻¹ • (fun x : d.κ → AF F => f (d.cmb (x ∘ τ.symm))) ∈ schA F d.κ :=
      Submodule.smul_mem _ _ (comp_schA τ.symm hf)
    refine ⟨e _, hbij.mapsTo hΨ, funext fun X => ?_⟩
    rw [hT _ hΨ]; simp only [Pi.smul_apply, smul_eq_mul]; rw [← mul_assoc, mul_inv_cancel₀ hC, one_mul]; congr 1
    conv_rhs => rw [← Adp.cmb_crd d X]
    congr 1; funext i; simp
  · obtain ⟨Ψ, hΨ, rfl⟩ := hbij.surjOn hΦ
    have hz : Ψ = 0 := funext fun v => by
      have := congrFun h0 (d.cmb (v ∘ τ.symm)); rw [hT Ψ hΨ, Adp.crd_cmb] at this; simpa [hC] using this
    rw [hz, map_zero]
end TBij_k
namespace KTunit
local instance (priority := high) {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    MeasurableSpace (κ → AF F) := borel _
local instance {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] : BorelSpace (κ → AF F) := ⟨rfl⟩
def cmap_k (d : SD_k σ) {κ : Type} (τ : κ ≃ TBij_k.Adp.Ix d) (X : d.MxE) : κ → AF F := fun k => d.crd X (τ k)
def cinv_k (d : SD_k σ) {κ : Type} (τ : κ ≃ TBij_k.Adp.Ix d) (c : κ → AF F) : d.MxE := d.cmb fun k => c (τ.symm k)
theorem cmap_cinv_k (d : SD_k σ) {κ : Type} (τ : κ ≃ TBij_k.Adp.Ix d) (c : κ → AF F) :
    cmap_k d τ (cinv_k d τ c) = c := funext fun _ => by simp [cmap_k, cinv_k, TBij_k.Adp.crd_cmb]
def cEquiv_k (d : SD_k σ) {κ : Type} (τ : κ ≃ TBij_k.Adp.Ix d) : d.MxE ≃ₜ+ (κ → AF F) where
  toFun := cmap_k d τ
  invFun := cinv_k d τ
  left_inv X := by
    have : (fun k => cmap_k d τ X (τ.symm k)) = d.crd X := funext fun _ => by simp [cmap_k]
    rw [cinv_k, this, TBij_k.Adp.cmb_crd]
  right_inv := cmap_cinv_k d τ
  map_add' _ _ := funext fun _ => by simp [cmap_k, SD_k.crd, map_add (f := _)]
  continuous_toFun := by
    have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    have hr := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)).2.2.2.2.2.2.1 2 d.bs
    exact continuous_pi fun k =>
      (continuous_apply (τ k).2.2).comp (hr.continuous.comp (continuous_id.matrix_elem (τ k).1 (τ k).2.1))
  continuous_invFun := by
    have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    let h := ((GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm
      (AF F)).2.2.2.2.2.2.1 2 d.bs).homeomorph
    have e : ∀ c i j, cinv_k d τ c i j = h.symm (fun l => c (τ.symm (i, j, l))) := fun c i j =>
      h.injective (by
        rw [Homeomorph.apply_symm_apply]
        exact funext fun l => congrFun (TBij_k.Adp.crd_cmb d (fun k => c (τ.symm k))) (i, j, l))
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [e]; exact h.symm.continuous.comp (continuous_pi fun l => continuous_apply _)
theorem map_haar_k (d : SD_k σ) {κ : Type} [Fintype κ] (τ : κ ≃ TBij_k.Adp.Ix d) (ν : Measure d.MxE)
    (hν : ν.IsAddHaarMeasure) :
    (ν.map (cmap_k d τ)).IsAddHaarMeasure ∧
      ∀ f : (κ → AF F) → ℂ, ∫ X, f (cmap_k d τ X) ∂ν = ∫ y, f y ∂(ν.map (cmap_k d τ)) := by
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have P := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)
  have : IsTopologicalRing (AE F E) := P.1; have : BorelSpace d.MxE := P.2.2.2.2.2.2.2.1 d.m d.n
  exact ⟨ContinuousAddEquiv.isAddHaarMeasure_map ν (cEquiv_k d τ),
    fun f => (integral_map_equiv (μ := ν) (cEquiv_k d τ).toHomeomorph.toMeasurableEquiv f).symm⟩
end KTunit
end
namespace KFP
namespace W
variable {d : SD_k σ}
private theorem cw_realAd (w : InfinitePlace F) {p q : Type} (r : ℝ) (X : Matrix p q (AE F E)) :
    d.cw w (realAd F r • X) = (r : ℂ) • d.cw w X :=
  GlobalTheory.RealScalar.realAd_smul_map σ d.B.emb d.cm X r w
private theorem actB_rot_vline (R : RD_k d) (t : ℝ) {W : d.MxE} (hW : finOne F • W = 0) (z : ℂ) :
    actB (cA σ) (rot_k R t) (vline_k R W z) = vline_k R W (Complex.exp (-(t * Complex.I)) * z) := by
  have htw := (exists_tw_k R W).choose_spec
  have hζ : R.ζ ≠ 0 := by rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
  have hline (w : InfinitePlace F) (P Q : d.MxE) :
      d.cw w (P * (incM F d.b.1.toCols₂)ᵀ + Q * (incM F d.b.1.toCols₁)ᵀ) =
        Matrix.fromCols (d.cw w Q) (d.cw w P) * (d.cw w (incM F d.b.1))ᵀ := by
    rw [cw_add'_k, cw_mul'_k, cw_mul'_k, cw_transpose'_k, cw_transpose'_k]
    conv_rhs => rw [← Matrix.fromCols_toCols (d.cw w (incM F d.b.1))]
    rw [Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, add_comm]; rfl
  have hf1 (x y : ℝ) : finOne F • ((realAd F x • W) * (incM F d.b.1.toCols₂)ᵀ +
      (realAd F y • tw_k R W) * (incM F d.b.1.toCols₁)ᵀ) = 0 := by
    rw [smul_add, ← Matrix.smul_mul, ← Matrix.smul_mul, smul_comm (finOne F) (realAd F x), hW,
      smul_comm (finOne F) (realAd F y), show finOne F • tw_k R W = 0 from htw.1]; simp
  unfold vline_k; rw [exp_mul_re', exp_mul_im']
  have hact : ∀ v : d.M2, actB (cA σ) (rot_k R t) v = v * (mat2 (rot_k R t))ᵀ := fun _ => rfl
  rw [hact]
  refine Place.cw_ext_k (d := d) (fun w => ?_) (by rw [← Matrix.smul_mul, hf1, hf1, Matrix.zero_mul])
  rw [cw_mul'_k, cw_transpose'_k, matrixRep_eq_frameConj, cw_mul'_k, cw_mul'_k, hline, hline,
    cw_realAd, cw_realAd, cw_realAd, cw_realAd, show d.cw w (tw_k R W) = _ from htw.2 w]
  have hinv : d.cw w (incM F ((d.b⁻¹ : GL d.N2 E) : Matrix _ _ E)) * d.cw w (incM F d.b.1) = 1 := by
    rw [← cw_mul'_k, incM_b_inv_mul_k, cw_one'_k]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ (d.cw w (incM F d.b.1))ᵀ, ← Matrix.transpose_mul, hinv, Matrix.transpose_one, Matrix.mul_one,
    rot_cols' d.n d.m hζ (R.sg w) t z.re z.im (d.cw w W) _ (dZ_cw_rot'_k R t w)]
private theorem exists_poly {Φ : d.Fn} (hΦ : d.KFin Φ) {k : d.G} (hk : k ∈ d.K) :
    ∃ q : Polynomial ℂ, q ≠ 0 ∧ ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0 := by
  set V := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ); have : FiniteDimensional ℂ V := hΦ.2
  have hmap : ∀ v ∈ V, d.om k v ∈ V := fun v hv => Submodule.span_induction (p := fun v _ => d.om k v ∈ V)
    (by rintro _ ⟨k', rfl⟩; exact Submodule.subset_span ⟨⟨k * k'.1, d.K.mul_mem hk k'.2⟩, by simp [map_mul]⟩)
    (by simp) (fun _ _ _ _ hx hy => by simpa using V.add_mem hx hy) (fun _ _ _ hx => by simpa using V.smul_mem _ hx) hv
  set f := (d.om k).restrict hmap
  have hpow (i : ℕ) (v : V) : (((f ^ i) v : V) : d.Fn) = d.om (k ^ i) v := by
    induction i generalizing v with
    | zero => simp
    | succ i ih => rw [pow_succ, mul_apply_eq_comp, ih, pow_succ, map_mul, mul_apply_eq_comp]; rfl
  refine ⟨minpoly ℂ f, minpoly.ne_zero (Algebra.IsIntegral.isIntegral f), ?_⟩
  have h0 := congrArg (fun g : Module.End ℂ V => ((g ⟨Φ, Submodule.subset_span ⟨1, by simp⟩⟩ : V) : d.Fn))
    (minpoly.aeval ℂ f)
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply, Submodule.coe_sum] at h0
  simpa only [LinearMap.smul_apply, Submodule.coe_smul, hpow, LinearMap.zero_apply, ZeroMemClass.coe_zero] using h0
private def jnpE (R : RD_k d) : Vw_k d × Yf_k d ≃ₜ+ d.MxE :=
  have hcmb : ∃ cF : Vw_k d × Yf_k d → (d.I3 → AF F), Continuous cF ∧
      (∀ p q, cF (p + q) = cF p + cF q) ∧ ∀ p, jn_k R p.1 p.2 = d.cmb (cF p) := by
    obtain ⟨L, hL⟩ := KFock.archEquiv_k d R
    let cF : Vw_k d × Yf_k d → (d.I3 → AF F) := fun p k =>
      (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (L.symm (zOf_k (EuclideanSpace.equiv (Iw_k d) ℝ p.1)) k)) (p.2 k) : AF F)
    have hcz : Continuous (fun u : Iw_k d → ℝ => zOf_k u) := continuous_pi fun w => continuous_pi fun a =>
      continuous_pi fun j => by
        rw [show (fun u : Iw_k d → ℝ => zOf_k u w a j) = fun u =>
          Complex.equivRealProdCLM.symm (u (w, a, j, true), u (w, a, j, false)) from rfl]
        exact Complex.equivRealProdCLM.symm.continuous.comp ((continuous_apply _).prodMk (continuous_apply _))
    refine ⟨cF, continuous_pi fun k => ?_, fun p q => funext fun k => Prod.ext ?_ rfl, fun p => ?_⟩
    · rw [show (fun p : Vw_k d × Yf_k d => cF p k) = fun p =>
          (Prod.mk ((GroundTheory.Global.homeomorphMixedSpace F).symm
          (L.symm (zOf_k (EuclideanSpace.equiv (Iw_k d) ℝ p.1)) k)) (p.2 k) : AF F) from
        funext fun _ => by simp only [cF]; rw [KFPB.homeo_symm_eq]]
      exact Continuous.prodMk ((GroundTheory.Global.homeomorphMixedSpace F).symm.continuous.comp
        ((continuous_apply k).comp (L.symm.continuous.comp
          (hcz.comp ((EuclideanSpace.equiv (Iw_k d) ℝ).continuous.comp continuous_fst)))))
        ((continuous_apply k).comp continuous_snd)
    · have hz : ∀ u v : Iw_k d → ℝ, zOf_k (u + v) = zOf_k u + zOf_k v := fun _ _ =>
        funext fun _ => funext fun _ => funext fun _ => Complex.ext (by simp [zOf_k]) (by simp [zOf_k])
      show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ + _
      rw [← map_add (f := _), Prod.fst_add, map_add (f := _), hz, map_add (f := _)]; rfl
    · refine (exists_jn_k R p.1 p.2).unique ⟨arc_jn_k R p.1 p.2, fin_jn_k R p.1 p.2⟩ ⟨?_, funext fun k => by
        show (d.crd (d.cmb (cF p)) k).2 = p.2 k; rw [KFock.crd_cmb'_k]⟩
      rw [arc_eq_iff_k]; intro w; rw [← hL (cF p) w,
        show (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (cF p k).1) =
          L.symm (zOf_k (EuclideanSpace.equiv (Iw_k d) ℝ p.1)) from funext fun _ => RingEquiv.apply_symm_apply _ _,
        ContinuousLinearEquiv.apply_symm_apply]
  { toFun := fun p => jn_k R p.1 p.2, invFun := fun X => (arc_k R X, fin_k d X)
    left_inv := fun p => Prod.ext (arc_jn_k R p.1 p.2) (fin_jn_k R p.1 p.2), right_inv := jn_arc_fin_k R
    map_add' := fun p q => by
      obtain ⟨cF, -, hadd, heq⟩ := hcmb
      show jn_k R (p + q).1 (p + q).2 = jn_k R p.1 p.2 + jn_k R q.1 q.2; rw [heq, heq, heq, hadd, KFock.cmb_add_k]
    continuous_toFun := by
      obtain ⟨cF, hc, -, heq⟩ := hcmb; show Continuous _; rw [funext heq]; exact (KFock.continuous_cmb_k d).comp hc
    continuous_invFun := by
      refine ((EuclideanSpace.equiv (Iw_k d) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)).prodMk
        (continuous_pi fun k => continuous_snd.comp ((continuous_apply k).comp (KFock.continuous_crd_k d)))
      have hloc : Continuous fun X : d.MxE => R.loc i.1 X i.2.1 i.2.2.1 := by
        unfold RD_k.loc; simp only [Matrix.map_apply, Matrix.mul_apply]
        exact continuous_star.comp (continuous_finsetSum _ fun l _ =>
          continuous_const.mul ((continuous_apply _).comp ((continuous_apply l).comp
            (Place.continuous_cw_k d i.1 (p := Fin d.m) (q := Fin d.n)))))
      split_ifs; exact Complex.continuous_re.comp hloc; exact Complex.continuous_im.comp hloc }
private theorem haar_jnp (R : RD_k d) :
    ∃ (νf : Measure (Yf_k d)) (ν : Measure d.MxE), νf.IsAddHaarMeasure ∧ ν.IsAddHaarMeasure ∧
      ∀ {f : d.MxE → ℂ}, f ∈ d.schM → ∀ {g : Yf_k d → ℂ}, g ∈ SB (Yf_k d) → ∀ {b : Vw_k d → ℂ},
        Continuous b → (∀ u, ‖b u‖ ≤ 1) →
        ∫ X, f X * star (b (arc_k R X) * g (fin_k d X)) ∂ν = ∫ u, star (b u) * hg_k R νf f g u := by
  obtain ⟨_, _, _, _⟩ := KFock.mxTop_k d
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  have : BorelSpace (Yf_k d) := Pi.borelSpace
  let νf : Measure (Yf_k d) := Measure.addHaar; set μ := (volume : Measure (Vw_k d)).prod νf
  let e : Vw_k d × Yf_k d ≃ᵐ d.MxE := (jnpE R).toHomeomorph.toMeasurableEquiv
  have hH : (Measure.map e μ).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ (jnpE R)
  refine ⟨νf, Measure.map e μ, inferInstance, hH, fun {f} hf {g} hg' {b} hb hb1 => ?_⟩
  have hfi : Integrable (fun p : Vw_k d × Yf_k d => f (jn_k R p.1 p.2)) μ :=
    (integrable_map_equiv e f).1 (KFock.int_schM_k d _ hH hf)
  obtain ⟨C, hC⟩ := hg'.1.continuous.bounded_above_of_compact_support hg'.2
  have hint : Integrable (fun p : Vw_k d × Yf_k d => f (jn_k R p.1 p.2) * star (b p.1 * g p.2)) μ :=
    hfi.mul_bdd (c := C)
      (continuous_star.comp ((hb.comp continuous_fst).mul (hg'.1.continuous.comp continuous_snd))).aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [norm_star, norm_mul]; exact (mul_le_mul (hb1 _) (hC _) (norm_nonneg _) zero_le_one).trans (one_mul C).le)
  rw [integral_map_equiv]; simp only [show ∀ p, e p = jn_k R p.1 p.2 from fun _ => rfl, arc_jn_k, fin_jn_k]
  rw [integral_prod _ hint]; refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [hg_k, star_mul]; rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun _ => by ring)
private def ev (w : Vw_k d) (z : ℂ) (u : Vw_k d) : ℂ :=
  2 * Real.pi * Complex.I * z.re * z.im * ((‖w‖ ^ 2 : ℝ) : ℂ) -
    4 * Real.pi * Complex.I * z.im * (⟪w, u⟫_ℝ + z.re * ((‖w‖ ^ 2 : ℝ) : ℂ)) +
    ((-(2 * Real.pi * (‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2)) : ℝ) : ℂ)
private theorem norm_add_smul_sq (w u : Vw_k d) (x : ℝ) :
    ‖u + x • w‖ ^ 2 = ‖u‖ ^ 2 + 2 * x * ⟪w, u⟫_ℝ + x ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm]; ring
private theorem T_vline (hH : THeis_k) (R : RD_k d) {g : Yf_k d → ℂ} {Ω : d.Fn} (hΩ : Ω ∈ d.sch)
    (hTΩ : d.T Ω = vac_k R g) {W : d.MxE} (hW : finOne F • W = 0) (z : ℂ) (X : d.MxE) :
    d.T (d.dd.rho d.B.ψ (vline_k R W z) Ω) X = star (Complex.exp (ev (arc_k R W) z (arc_k R X))) * g (fin_k d X) := by
  have hlocA (w : InfinitePlace F) (A B : d.MxE) : R.loc w (A + B) = R.loc w A + R.loc w B := by
    simp only [RD_k.loc, cw_add'_k, Matrix.mul_add]; exact Matrix.map_add _ (fun a b => star_add a b) _ _
  have hlocS (w : InfinitePlace F) (t : ℝ) (A : d.MxE) : R.loc w (realAd F t • A) = (t : ℂ) • R.loc w A := by
    simp only [RD_k.loc, cw_realAd, Matrix.mul_smul]; ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [star_mul', Complex.star_def, Complex.conj_ofReal]; rfl
  have harcA (A B : d.MxE) : arc_k R (A + B) = arc_k R A + arc_k R B := by
    unfold arc_k
    rw [show (fun i : Iw_k d => if i.2.2.2 then (R.loc i.1 (A + B) i.2.1 i.2.2.1).re else
        (R.loc i.1 (A + B) i.2.1 i.2.2.1).im) =
      (fun i : Iw_k d => if i.2.2.2 then (R.loc i.1 A i.2.1 i.2.2.1).re else (R.loc i.1 A i.2.1 i.2.2.1).im) +
      (fun i : Iw_k d => if i.2.2.2 then (R.loc i.1 B i.2.1 i.2.2.1).re else (R.loc i.1 B i.2.1 i.2.2.1).im) from
      funext fun i => by simp only [hlocA, Pi.add_apply]; split_ifs <;> simp]
    exact map_add (EuclideanSpace.equiv (Iw_k d) ℝ).symm _ _
  have harcS (t : ℝ) (A : d.MxE) : arc_k R (realAd F t • A) = t • arc_k R A := by
    unfold arc_k
    rw [show (fun i : Iw_k d => if i.2.2.2 then (R.loc i.1 (realAd F t • A) i.2.1 i.2.2.1).re else
        (R.loc i.1 (realAd F t • A) i.2.1 i.2.2.1).im) =
      t • (fun i : Iw_k d => if i.2.2.2 then (R.loc i.1 A i.2.1 i.2.2.1).re else (R.loc i.1 A i.2.1 i.2.2.1).im) from
      funext fun i => by simp only [hlocS, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp]
    exact map_smul (EuclideanSpace.equiv (Iw_k d) ℝ).symm _ _
  have hfinA : fin_k d (X + realAd F z.re • W) = fin_k d X := by
    have h0 : fin_k d (realAd F z.re • W) = 0 := (fin_eq_zero_iff_k _).2 (by rw [smul_comm, hW, smul_zero])
    funext k; show (d.crd (X + realAd F z.re • W) k).2 = (d.crd X k).2
    rw [TBij_k.Adp.crd_add]; change (d.crd X k).2 + fin_k d (realAd F z.re • W) k = _; rw [h0, Pi.zero_apply, add_zero]
  have hgau (Y : d.MxE) : gau_k R Y = (Real.exp (-(2 * Real.pi * ‖arc_k R Y‖ ^ 2)) : ℂ) := by
    have hn : ‖arc_k R Y‖ ^ 2 = ∑ w, ∑ a, ∑ i, ‖R.loc w Y a i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, arc_k, Real.norm_eq_abs, sq_abs]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      simp only [EuclideanSpace.equiv]; rw [Complex.sq_norm, Complex.normSq_apply]; simp [sq]
    simp only [gau_k, fP, evX, map_one, one_mul, gs]; rw [hn, ← Complex.exp_sum, Complex.ofReal_exp]
    congr 1; push_cast; rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  unfold vline_k
  rw [T_rho_sum'_k hH hΩ, psi_sp'_k R hW, psi_tw'_k R hW, hTΩ]; simp only [vac_k]
  rw [hgau, harcA, harcS, hfinA, show star (Complex.exp _) = Complex.exp (conj _) from (Complex.exp_conj _).symm,
    Complex.ofReal_exp, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2; rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_add_smul_sq]
  simp only [ev, map_add (f := _), map_sub, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
end W
theorem kFinPoly_of_k (hT : TAll_k) (hU : TUnit_k) (hH : THeis_k) (_ : SiegelWeilDatumProperties) (hF : FockMem_k)
    (hLO : LocOpEx_k) (hLI : LocInst_k) : KFinPoly_k := by
  intro F E _ _ _ _ _ σ d R Φ hK; have hΦ := hK.1
  obtain ⟨νf, ν, hνf, hν, hint_jnp⟩ := W.haar_jnp R
  obtain ⟨χ, hχ, heig⟩ := om_rot_vac'_k hT hLO hLI R 1
  set s : ℝ := -(4 * Real.pi); have hs : s ≠ 0 := neg_ne_zero.2 (by positivity); set c : ℝ := 1 / (16 * Real.pi)
  let W₀ : Vw_k d → d.MxE := fun ξ => jn_k R (s⁻¹ • ξ) 0
  have hW (ξ) : finOne F • W₀ ξ = 0 := (fin_eq_zero_iff_k _).1 (fin_jn_k R _ _)
  have hsW (ξ) : s • arc_k R (W₀ ξ) = ξ := by simp only [W₀, arc_jn_k, smul_smul, mul_inv_cancel₀ hs, one_smul]
  set k := rot_k R 1; set ω : ℂ := Complex.exp (-((1 : ℝ) * Complex.I))
  let vv : Vw_k d → ℂ → d.M2 := fun ξ z => vline_k R (W₀ ξ) z
  have hω1 : ‖ω‖ = 1 := by rw [Complex.norm_exp]; simp
  have hω0 : ω ≠ 0 := fun h => by rw [h, norm_zero] at hω1; exact zero_ne_one hω1
  have hω (j : ℕ) (hj : 0 < j) (h : ω ^ j = 1) : False := by
    rw [← Complex.exp_natCast_mul, Complex.exp_eq_one_iff] at h; obtain ⟨m, hm⟩ := h
    have h3 : -(j : ℝ) = 2 * Real.pi * m := by have := congrArg Complex.im hm; simp at this; linarith
    have hm0 : (m : ℝ) ≠ 0 := fun h0 => by rw [h0, mul_zero, neg_eq_zero] at h3; exact (Nat.cast_pos.2 hj).ne' h3
    refine irrational_pi ⟨-(j : ℚ) / (2 * m), ?_⟩; push_cast; field_simp; linarith
  have hrot (ξ z) : actB (cA σ) k (vv ξ z) = vv ξ (ω * z) := W.actB_rot_vline R 1 (hW ξ) z
  have hB : ∀ g ∈ SB (Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = vac_k R g → ∀ Ψ ∈ d.sch, ∀ ξ z,
      B_k ν Ψ (d.dd.rho d.B.ψ (vv ξ z) Ω) = (Real.exp (-(c * ‖z‖ ^ 2 * ‖ξ‖ ^ 2)) : ℂ) *
        (Complex.exp (-(z ^ 2 * ‖ξ‖ ^ 2 / (16 * Real.pi))) *
          ∫ u, hg_k R νf (d.T Ψ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ)) := by
    intro g hg' Ω hΩ hTΩ Ψ hΨ ξ z; set w := arc_k R (W₀ ξ)
    let b : Vw_k d → ℂ := fun u => star (Complex.exp (W.ev w z u))
    have hinn : Continuous fun u : Vw_k d => ⟪w, u⟫_ℝ := continuous_const.inner continuous_id
    have hb : Continuous b := continuous_star.comp (Complex.continuous_exp.comp
      ((continuous_const.sub (continuous_const.mul ((Complex.continuous_ofReal.comp hinn).add continuous_const))).add
        (Complex.continuous_ofReal.comp (continuous_const.mul
          (((continuous_norm.pow 2).add (continuous_const.mul hinn)).add continuous_const)).neg)))
    have hb1 (u) : ‖b u‖ ≤ 1 := by
      rw [show b u = star (Complex.exp (W.ev w z u)) from rfl, norm_star, Complex.norm_exp]
      apply Real.exp_le_one_iff.2
      have h : ‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2 ≥ 0 := by rw [← W.norm_add_smul_sq]; positivity
      simp only [W.ev, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.mul_im]
      nlinarith [Real.pi_pos]
    have e1 : B_k ν Ψ (d.dd.rho d.B.ψ (vv ξ z) Ω) = ∫ u, star (b u) * hg_k R νf (d.T Ψ) g u := by
      simp only [B_k, vv, W.T_vline hH R hΩ hTΩ (hW ξ) z]; exact hint_jnp ((hT.1 F E σ d).1 Ψ hΨ) hg' hb hb1
    rw [e1, ← hsW ξ]
    have key (u) : star (b u) * hg_k R νf (d.T Ψ) g u =
        ((Real.exp (-(c * ‖z‖ ^ 2 * ‖s • w‖ ^ 2)) : ℝ) : ℂ) *
          Complex.exp (-(z ^ 2 * (‖s • w‖ ^ 2 : ℝ) / (16 * Real.pi))) *
            (hg_k R νf (d.T Ψ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) * Complex.exp (z * ⟪s • w, u⟫_ℝ)) := by
      have h1 := exp_alg z.re z.im (‖w‖ ^ 2) ⟪w, u⟫_ℝ (‖u‖ ^ 2); rw [Complex.re_add_im z] at h1
      have hn : ‖s • w‖ ^ 2 = 16 * Real.pi ^ 2 * ‖w‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
      have hi : ⟪s • w, u⟫_ℝ = -(4 * Real.pi) * ⟪w, u⟫_ℝ := real_inner_smul_left _ _ _
      have hzn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
      simp only [b, star_star, hn, hi, hzn, c, s]; unfold W.ev; rw [h1]; ring
    simp_rw [key]; rw [integral_const_mul, Complex.ofReal_exp]; push_cast; ring
  obtain ⟨q, hq0, hq⟩ := W.exists_poly hK (rot_mem_k R 1)
  obtain ⟨N, hN⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFPB.poly_of_rot q hq0 (star χ)⁻¹ ω⁻¹ (inv_ne_zero (star_ne_zero.2 hχ)) (inv_ne_zero hω0)
    fun j hj h => hω j hj (by rw [inv_pow] at h; exact inv_eq_one.1 h)
  have hmul (a b : d.G) (u : d.M2) : actB (cA σ) (a * b) u = actB (cA σ) a (actB (cA σ) b u) := by
    simp only [actB, Units.val_mul, Subgroup.coe_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  have hinv (ξ z) : actB (cA σ) k⁻¹ (vv ξ z) = vv ξ (ω⁻¹ * z) := by
    have := congrArg (actB (cA σ) k⁻¹) (hrot ξ (ω⁻¹ * z))
    rwa [← hmul, inv_mul_cancel, show ∀ u : d.M2, actB (cA σ) (1 : d.G) u = u from fun _ => by simp [actB],
      ← mul_assoc, mul_inv_cancel₀ hω0, one_mul, eq_comm] at this
  have hact (i : ℕ) (ξ z) : actB (cA σ) (k⁻¹ ^ i) (vv ξ z) = vv ξ (ω⁻¹ ^ i * z) := by
    induction i generalizing z with
    | zero => simp [actB]
    | succ i ih => rw [pow_succ, hmul, hinv, ih, pow_succ, mul_assoc]
  have hTΦ := (hT.1 F E σ d).1 Φ hΦ
  refine KFP.OswGen.mem_fock_of_k R hνf hTΦ fun g hg' => ?_
  obtain ⟨Ω, hΩ, hTΩ⟩ := exists_lift_k hT hF R hg'; obtain ⟨h, hh⟩ := KFP.OswGen.hg_sch_k R hνf hTΦ hg'
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨P, -, hP⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFPB.poly_gauss_of_lines (2 * Real.pi) hpi N h fun ξ => by
    set I : ℂ → ℂ := fun z => ∫ u, h u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) * Complex.exp (z * ⟪ξ, u⟫_ℝ)
    set Eξ : ℂ → ℂ := fun z => Complex.exp (-(z ^ 2 * ‖ξ‖ ^ 2 / (16 * Real.pi))) * I z
    have hrel (z) : ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (star χ)⁻¹ ^ i * Eξ (ω⁻¹ ^ i * z) = 0 := by
      have e0 := B_rel'_k hT hU hν hχ hΩ (heig g hg' Ω hΩ hTΩ) hΦ q hq (vv ξ z)
      simp only [hact, hB g hg' Ω hΩ hTΩ Φ hΦ, ← hh, show ∀ i : ℕ, ‖ω⁻¹ ^ i * z‖ = ‖z‖ from fun _ => by
        rw [norm_mul, norm_pow, norm_inv, hω1, inv_one, one_pow, one_mul]] at e0
      have hc0 : (Real.exp (-(c * ‖z‖ ^ 2 * ‖ξ‖ ^ 2)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
      refine (mul_eq_zero.1 (?_ : (Real.exp (-(c * ‖z‖ ^ 2 * ‖ξ‖ ^ 2)) : ℂ) *
        ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (star χ)⁻¹ ^ i * Eξ (ω⁻¹ ^ i * z) = 0)).resolve_left hc0
      rw [Finset.mul_sum, ← e0]; exact Finset.sum_congr rfl fun _ _ => by simp only [Eξ, I]; ring
    obtain ⟨p, hpN, hp⟩ := hN Eξ ((Differentiable.cexp (((differentiable_id.pow 2).mul_const _).div_const _).neg).mul
      (_root_.PositivityTheory.SiegelWeilFormula.KFPB.entire_laplace (2 * Real.pi) hpi h ξ)) hrel
    refine ⟨p, hpN, fun z => ?_⟩
    have e2 : I z = Complex.exp (z ^ 2 * ‖ξ‖ ^ 2 / (16 * Real.pi)) * p.eval z := by
      rw [← hp z, ← mul_assoc, ← Complex.exp_add]; simp
    rw [show ((8 : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) = 16 * (Real.pi : ℂ) by push_cast; ring]; simpa [I] using e2
  exact ⟨P, fun u => by rw [← hh]; exact hP u⟩
end KFP
namespace KSplit
open KSplitA
private theorem exists_embU_loc (d : SD_k σ) (R : RD_k d) (w : InfinitePlace F) (u : Matrix (Fin d.m) (Fin d.m) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin d.m) ℂ) : ∃ g : UA σ d.A.J, ∀ X : d.MxE,
      R.loc w (mat g⁻¹ * X) = (u * Matrix.of (R.loc w X) : Matrix (Fin d.m) (Fin d.n) ℂ) ∧
        (∀ w', w' ≠ w → d.cw w' (mat g⁻¹ * X - X) = 0) ∧ finOne F • (mat g⁻¹ * X - X) = 0 := by
  set fr := (R.fr w).1; set fri := ((R.fr w)⁻¹).1
  have hb : fr * fri = 1 := (by simp [fr, fri]); have hb' : fri * fr = 1 := by simp [fr, fri]
  have huu : u * uᴴ = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hu
  have huu' : uᴴ * u = 1 := by rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hu
  set h := u.map star; have hhs : h.map star = u := by ext _ _; simp [h]
  have hht : hᵀ = uᴴ := by ext _ _; simp [h, Matrix.conjTranspose_apply]
  have h1 : h * uᵀ = 1 := by rw [show h * uᵀ = (u * uᴴ)ᵀ by rw [Matrix.transpose_mul]; rfl, huu, Matrix.transpose_one]
  have h2 : uᵀ * h = 1 := by rw [show uᵀ * h = (uᴴ * u)ᵀ by rw [Matrix.transpose_mul]; rfl, huu', Matrix.transpose_one]
  set Z := fr * h * fri; set Z' := fr * uᵀ * fri
  have hZZ : Z * Z' = 1 := by
    simp only [Z, Z', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc fri fr, hb', Matrix.one_mul, ← Matrix.mul_assoc h uᵀ, h1, Matrix.one_mul, hb]
  have hZZ' : Z' * Z = 1 := by
    simp only [Z, Z', Matrix.mul_assoc]
    rw [← Matrix.mul_assoc fri fr, hb', Matrix.one_mul, ← Matrix.mul_assoc uᵀ h, h2, Matrix.one_mul, hb]
  have hζ0 : R.ζ ≠ 0 := by rcases R.hζ with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> simp
  set D := d.A.J.map (d.B.emb w).1; set Q := frᵀ * D * fr.map star
  have hhQ : hᵀ * Q * h.map star = Q := smul_right_injective _ hζ0 <| by
    show R.ζ • (hᵀ * Q * h.map star) = R.ζ • Q
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, R.hfr w, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hhs, hht, huu']
  have hmem : (Krd.atM_k d w Z)ᵀ * incM F d.A.J * (Krd.atM_k d w Z).map (cA σ) = incM F d.A.J := by
    refine Place.cw_ext_k d (fun w' => ?_) ?_
    · rw [Krd.cw_mul_k, Krd.cw_mul_k, Place.cw_cA_k, Krd.cw_transpose_k, Krd.cw_incM_k, Krd.cw_atM_k]
      unfold Krd.fam; split_ifs with hw
      · subst hw; exact Krd.conj_unit fr fri h D Q hb rfl hhQ
      · rw [Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
    · have e1 : (finOne F • (1 : Matrix (Fin d.m) (Fin d.m) (AE F E))).map (cA σ) = finOne F • 1 := by
        rw [Krd.map_cA_smul, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [Krd.fin_mul, Krd.fin_mul, ← Matrix.transpose_smul, Krd.fin_atM_k, ← Krd.map_cA_smul, Krd.fin_atM_k, e1,
        Matrix.transpose_smul, Matrix.transpose_one, ← Krd.fin_mul, ← Krd.fin_mul, Matrix.mul_one, Matrix.one_mul]
  let k : UA σ d.A.J := ⟨⟨Krd.atM_k d w Z, Krd.atM_k d w Z', by rw [← Krd.atM_mul_k, hZZ, Krd.atM_one_k],
    by rw [← Krd.atM_mul_k, hZZ', Krd.atM_one_k]⟩, hmem⟩
  have hcwm (w' : InfinitePlace F) (A : Matrix (Fin d.m) (Fin d.m) (AE F E)) (B : d.MxE) :
      d.cw w' (A * B) = d.cw w' A * d.cw w' B := Matrix.map_mul
  refine ⟨k⁻¹, fun X => ⟨?_, fun w' hw' => ?_, ?_⟩⟩
  · rw [inv_inv]; show (fri * d.cw w (Krd.atM_k d w Z * X)).map star = u * (fri * d.cw w X).map star
    rw [hcwm, Krd.cw_atM_k]; simp only [Krd.fam, ite_true, Z]
    rw [show fri * (fr * h * fri * d.cw w X) = (fri * fr) * h * (fri * d.cw w X) by simp only [Matrix.mul_assoc],
      hb', Matrix.one_mul, mapStar_mul', hhs]
  · rw [inv_inv]; show d.cw w' (Krd.atM_k d w Z * X - X) = 0
    rw [show ∀ A B : d.MxE, d.cw w' (A - B) = d.cw w' A - d.cw w' B from fun _ _ => by ext _ _; simp [SD_k.cw],
      hcwm, Krd.cw_atM_k]
    simp only [Krd.fam, ite_eq_right hw', Matrix.one_mul, sub_self]
  · rw [inv_inv]; show finOne F • (Krd.atM_k d w Z * X - X) = 0
    rw [smul_sub, ← Matrix.smul_mul, Krd.fin_atM_k, Matrix.smul_mul, Matrix.one_mul, sub_self]
private theorem I_S_loc (d : SD_k σ) (hT : TAll_k) (Φ : d.Fn) (hΦ : Φ ∈ d.sch) (g : UA σ d.A.J) (x : d.G) :
    d.I (d.S g Φ) x = d.I Φ x := by
  have := d.ok.haar; have := PositivityTheory.ThKF.countable_ratU σ d.A.J; have : BorelSpace (UA σ d.A.J) := ⟨rfl⟩
  have hsym : ∃ ε : ℤˣ, ∀ i j, σ (d.A.J j i) = ((ε : ℤ) : E) * d.A.J i j := d.ok.sign.elim
    (fun ⟨h, _⟩ => ⟨1, fun _ _ => by rw [h.herm]; simp⟩) (fun ⟨h, _⟩ => ⟨-1, fun _ _ => by rw [h.skew]; simp⟩)
  have hdet : d.A.J.det ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have key : (d.A.J.map (d.B.emb w).1).det ≠ 0 := d.ok.sign.elim (fun ⟨h, _⟩ => det_ne_of_hasSig (h.sig w))
      (fun ⟨h, _⟩ => by
        have := det_ne_of_hasSig (h.sig w); rw [Matrix.det_smul] at this; exact right_ne_zero_of_mul this)
    intro h0; apply key
    rw [show d.A.J.map (d.B.emb w).1 = ((d.B.emb w).1 : E →+* ℂ).mapMatrix d.A.J from rfl,
      ← RingHom.map_det, h0, map_zero]
  obtain ⟨ε, hε⟩ := hsym
  have : d.μ.IsMulRightInvariant :=
    (PositivityTheory.ThKF.unimodularity_holds F E σ d.cm d.m d.A.J ε hε hdet).2.2 d.μ d.ok.haar
  have hrat : ∀ Ψ ∈ d.sch, ∀ γ ∈ ratU σ d.A.J, thetaSum F (d.S γ Ψ) = thetaSum F Ψ := fun Ψ hΨ γ ⟨γ0, hγ0⟩ => by
    have h1 := (hT.2.2.2.1 F E σ d (d.S γ Ψ) (d.ok.dbl.lin.pres γ Ψ hΨ)).1
    have hm : mat γ⁻¹ = incM F (γ0⁻¹).1 := by
      have hγ1 : ((γ : UA σ d.A.J) : GL (Fin d.m) (AE F E)) =
          Matrix.GeneralLinearGroup.map (inclR (AF F)) γ0 := hγ0.symm
      show ((γ⁻¹ : UA σ d.A.J).1).1 = _; rw [Subgroup.coe_inv, hγ1, ← map_inv]; rfl
    have e (X : d.ME) : d.T (d.S γ Ψ) (incM F X) = d.T Ψ (incM F ((γ0⁻¹).1 * X)) := by
      rw [(hT.2.1 F E σ d Ψ hΨ).2.2 γ (incM F X), hm]; simp only [incM, Matrix.map_mul]
    simp only [e] at h1
    let eqv : d.ME ≃ d.ME := ⟨fun X => (γ0⁻¹).1 * X, fun X => γ0.1 * X,
      fun X => by dsimp only; simp [← Matrix.mul_assoc], fun X => by dsimp only; simp [← Matrix.mul_assoc]⟩
    exact ((eqv.hasSum_iff (f := fun X => d.T Ψ (incM F X))).1 h1).unique (hT.2.2.2.1 F E σ d Ψ hΨ).1
  have hinv (γ) (hγ : γ ∈ ratU σ d.A.J) (h) : thetaSum F (d.om x (d.S (γ * h) Φ)) = thetaSum F (d.om x (d.S h Φ)) := by
    have hSh := d.ok.dbl.lin.pres h _ hΦ
    rw [map_mul, mul_apply_eq_comp, (hT.2.2.2.1 F E σ d _ hSh).2 x γ, hrat _ (d.ok.dbl.weil.2.1.pres _ _ hSh) γ hγ]
  simp only [SD_k.I, thetaMean, setAverage_eq, show ∀ h, thetaSum F (d.om x (d.S h (d.S g Φ))) =
    thetaSum F (d.om x (d.S (h * g) Φ)) from fun h => by rw [map_mul, mul_apply_eq_comp]]
  rw [PositivityTheory.ThKF.L2.integral_right d.ok.dom (fun h => thetaSum F (d.om x (d.S h Φ))) hinv g]
theorem gIinv_of_k : TAll_k → FockMem_k → GIinv_k := by
  intro hT hF F E _ _ _ _ _ σ d R w Ψ hΨ φ hφ g a b P
  let Λ : PX d.m d.n →ₗ[ℂ] ℂ :=
    { toFun := fun P => d.I (φ P) g
      map_add' := fun P Q => by
        rw [map_add (f := _), Atop.I_add d hT.2.2.2.1 hT.2.2.2.2 (hφ P).1 (hφ Q).1]; rfl
      map_smul' := fun c P => by rw [map_smul, Atop.I_smul d hT.2.2.2.1 c (hφ P).1]; rfl }
  refine hOp_kill Λ (fun u hu P => ?_) (2 * Real.pi) a b P
  obtain ⟨g', hg'⟩ := exists_embU_loc d R w u hu
  have hP := hφ P; have hQ := hφ (actU u P)
  have hsub : d.S g' (φ P) + (-1 : ℂ) • φ (actU u P) ∈ d.sch :=
    d.sch.add_mem (d.ok.dbl.lin.pres _ _ hP.1) (d.sch.smul_mem _ hQ.1)
  have hT0 : d.T (d.S g' (φ P) + (-1 : ℂ) • φ (actU u P)) = 0 := by
    rw [KFock.T_add_k, KFock.T_smul_k]; funext X
    rw [Pi.add_apply, Pi.smul_apply, (hT.2.1 F E σ d (φ P) hP.1).2.2 g' X, hP.2, hQ.2]
    obtain ⟨h1, h2, h3⟩ := hg' X; simp only [RD_k.tens, smul_eq_mul, Pi.zero_apply]
    rw [h1, show mat g'⁻¹ * X = X + (mat g'⁻¹ * X - X) by abel, ((hF F E σ d R).2.1 w Ψ hΨ).2 X _ h2 h3,
      show fP P (u * Matrix.of (R.loc w X)) = fP (actU u P) (R.loc w X) from _root_.PositivityTheory.SiegelWeilFormula.KSplitA.fP_unitary u hu P _]; ring
  have heq : d.S g' (φ P) = φ (actU u P) := by
    have := eq_neg_of_add_eq_zero_left ((hT.1 F E σ d).2.2 _ hsub hT0); rwa [neg_smul, one_smul, neg_neg] at this
  show d.I (φ (actU u P)) g = d.I (φ P) g; rw [← heq, I_S_loc d hT _ hP.1 g' g]
theorem gSplit_of_k (hF : FockMem_k) (hAw : AwayAct_k) : GSplit_k := by
  intro F E _ _ _ _ _ σ d R w L hL Ψ hΨ φ hφ g
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa g; obtain ⟨y, hk'K, hk'w⟩ := KSplitW.kSplit_k d R w k hk
  set k' := (R.ι w y)⁻¹ * k with hk'; have hcomm := KSplitW.commW_k d R w k' hk'w
  obtain ⟨A, hA⟩ := hAw F E σ d R w k' hk'w; have hΨi : d.Indep w Ψ := ((hF F E σ d R).2.1 w Ψ hΨ).2
  obtain ⟨C, hC⟩ := KSplitP.siegel_k d hp
  refine ⟨p * k', y, C * A Ψ 0, (GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ),
    KSplitP.absE_pos _, by rw [mul_assoc, hcomm y, hk', mul_inv_cancel_left], fun y' => ⟨?_, fun P => ?_⟩⟩
  · obtain ⟨q, k₀, rfl, hq, hk₀, hloc⟩ := Glob.locIwasawa y'
    obtain ⟨tq, hPq, habs⟩ := KSplitP.iota_isPar_k d R w q hq
    have e : p * k' * R.ι w (q * k₀) = (p * R.ι w q) * (R.ι w k₀ * k') := by
      rw [map_mul, mul_assoc p, ← mul_assoc k', hcomm q, mul_assoc (R.ι w q), hcomm k₀]; simp only [mul_assoc]
    have hval := d.ok.hgt.val _ _ (KSplitP.isPar_mul hp hPq) _ ((d.K).mul_mem (KSplitW.iota_mem_K_k d R w k₀ hk₀) hk'K)
    show ((d.a (p * k' * R.ι w (q * k₀))).toNNReal : ℝ) = _
    rw [e, Real.coe_toNNReal _ (by rw [hval]; exact NNReal.coe_nonneg _), hval, map_mul, map_mul, NNReal.coe_mul,
      habs, hloc]
  · have hsw := KFock.isSw_fP P; have hΞ := (hL y' (fP P) hsw).2 Ψ hΨi (φ P) (hφ P).1 (hφ P).2
    have hΞs := d.om_sch (R.ι w y') (φ P) (hφ P).1; have h2 := (hA Ψ hΨi).2 _ (hL y' (fP P) hsw).1 _ hΞs hΞ
    unfold SD_k.sec0
    rw [map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, hC _ (d.om_sch _ _ hΞs),
      ← KSplitP.T_zero_k, h2]; simp only [RD_k.tens, KSplitP.loc_zero_k]; ring
end KSplit
end PositivityTheory.SiegelWeilFormula
end
