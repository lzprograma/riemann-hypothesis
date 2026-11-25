module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoRows
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicWeilRepSchrodingerModelUnique
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Prelims.DoublingPairLatticeTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilHeightdictStd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKTunitMeas
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.DarbouxAnti
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.BlockIndexInrLast
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ChartA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ChartB
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.EmbQMapApply
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SchrodingerCommutation.DetWeylBlockNeZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.InvMulSelfMatrixDoubled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegelStatement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinateChangeRealisedWithDouble
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin

/-! # SiegelWeilAldChart: Consolidated global theta-kernel definitions and proofs (SiegelWeilAldChart). -/
@[expose] public section

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw GlobalTheory.HeisSchA
open GlobalTheory.Doubling (absE)
open Matrix (GeneralLinearGroup fromBlocks fromBlocks_multiply fromBlocks_one fromCols transpose_mul)

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem chartFacts_k : ChartFacts_k := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' h0 h'
  have rdE : ∀ w, (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e w = ((dd0.e w).1 ∘ eK d.m h,
      (dd0.e w).2 ∘ eK d.m h) :=
    fun w => by rw [GlobalTheory.TowU.reindexD_e, Equiv.symm_symm]
  have hfr : ∀ g, inFrame d.b (j g) = blk h (inFrame b g) 1 := fun g => eq_blk h _ _ (hj.2.1 g) (hj.2.2 g)
  refine ⟨fun w' => ?_, fun u v => ⟨_, LinearEquiv.apply_symm_apply _ _⟩, fun g w H1 H2 => ?_, fun g w' => ?_,
    fun u w' => ?_⟩
  ·
    rw [rdE, adapted_e h0, frQ_emb, embQ_toCols₁, embQ_toCols₂, adapted_e h']
    refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
    · rcases q with ⟨a, c, t⟩ | ⟨a, t⟩
      · exact crdB_col _ _ _ a _ c t (extend_zero_embedded_column h _ a c)
      · exact crdB_zero_col _ _ a _ t (extend_zero_last_column h _ a)
    · rcases q with ⟨a, c, t⟩ | ⟨a, t⟩
      · exact Bf_col _ _ _ _ a _ c t (fun p => extend_zero_embedded_column h _ p c)
      · exact Bf_zero_col _ _ _ a _ t (fun p => extend_zero_last_column h _ p)
  ·
    set Q := frQ d.b w with hQdef
    set Q' := Q.submatrix id (Sum.map (em0 h) (em0 h)) with hQ'def
    have hw := adapted_e h0 w
    have hz : dd0.e (embQ h Q' * (incM F d.b.1)ᵀ) = 0 := by
      rw [adapted_e h0, frQ_of, embQ_toCols₁, embQ_toCols₂]
      refine Prod.ext (funext fun q => ?_) (funext fun q => ?_)
      · obtain ⟨a, c, t⟩ := q
        by_cases hc : c = i0 h
        · subst hc
          exact crdB_zero_col _ _ a _ t (extend_zero_last_column h _ a)
        · obtain ⟨c', rfl⟩ := (ne_last_iff_mem_range h c).1 hc
          have e3 := congrFun H1 (a, c', t)
          rw [rdE, hw] at e3
          refine (crdB_col _ _ _ a _ _ t ?_).trans e3
          rw [extend_zero_embedded_column]
          rfl
      · obtain ⟨a, c, t⟩ := q
        by_cases hc : c = i0 h
        · subst hc
          exact Bf_zero_col _ _ _ a _ t (fun p => extend_zero_last_column h _ p)
        · obtain ⟨c', rfl⟩ := (ne_last_iff_mem_range h c).1 hc
          have e3 := congrFun H2 (a, c', t)
          rw [rdE, hw] at e3
          refine (Bf_col _ _ _ _ a _ _ t fun p => ?_).trans e3
          rw [extend_zero_embedded_column]
          rfl
    have hQ' : embQ h Q' = 0 := by
      have := (LinearEquiv.map_eq_zero_iff dd0.e).1 hz
      rw [← frQ_of d.b (embQ h Q'), this, frQ, Matrix.zero_mul]
    have hQv : ∀ a v', Q a (Sum.map (em0 h) (em0 h) v') = 0 := fun a v' => by
      have := congrFun (congrFun hQ' a) (Sum.map (em0 h) (em0 h) v')
      rwa [embQ_map_apply] at this
    apply frQ_injective d.b
    show frQ d.b (w * ((j g).1.1)ᵀ) = frQ d.b w
    rw [frQ_mul_mat, hfr, ← hQdef]
    ext a u
    rw [Matrix.mul_apply]
    have hterm : ∀ v, Q a v * (blk h (inFrame b g) 1)ᵀ v u = Q a v * (1 : Matrix d.N2 _ (AE F E)) u v :=
        by
      intro v
      rcases idx_cases h v with ⟨v', rfl⟩ | hv | hv
      · rw [hQv, zero_mul, zero_mul]
      · rw [Matrix.transpose_apply, (blk_out h _ v (by rw [hv]; exact Or.inl rfl) u).2]
      · rw [Matrix.transpose_apply, (blk_out h _ v (by rw [hv]; exact Or.inr rfl) u).2]
    rw [Finset.sum_congr rfl fun v _ => hterm v]
    simp [Matrix.one_apply]
  ·
    apply frQ_injective d.b
    show frQ d.b (emb h b d.b w' * ((j g).1.1)ᵀ) = frQ d.b (emb h b d.b (w' * (g.1.1)ᵀ))
    rw [frQ_mul_mat, frQ_emb, frQ_emb, frQ_mul_mat, hfr, embQ_mul_blk]
  ·
    rw [emb_eq, emb_eq, frQ_left, ← embQ_mul_left, Matrix.mul_assoc]
end PositivityTheory.SiegelWeilFormula.Ald
end

section
namespace PositivityTheory.SiegelWeilFormula.tweyl
variable (d : SD_k σ)
theorem std_k : IsStd d.B.ψ := d.ok.good.std
include d in
theorem cm_k : IsCMExt F E σ := d.ok.good.1
theorem hS_k : IsUSplitting (adeleClass F) d.B.ψ d.dd (fun (g : UA σ d.A.J) x => mat g * x) d.S := d.ok.dbl.lin
theorem hO_k : IsUSplitting (adeleClass F) d.B.ψ d.dd (actB (cA σ)) d.om := d.ok.dbl.weil.2.1
theorem hR_k : SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) d.dd d.χ
    (diagCols (Fin d.n)) d.om := d.ok.dbl.weil.2.2
theorem mat_mul_inv_k (g : UA σ d.A.J) : mat g * mat g⁻¹ = 1 := by
  show g.1.1 * (g⁻¹).1.1 = 1
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
end PositivityTheory.SiegelWeilFormula.tweyl
end
end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section
set_option linter.unusedSectionVars false
namespace PositivityTheory.SiegelWeilFormula.tweyl
variable (d : SD_k σ)
theorem actB_conj_k (x : d.G) (g : UA σ d.A.J) (v : d.M2) :
    actB (cA σ) x⁻¹ (mat g * actB (cA σ) x (mat g⁻¹ * v)) = v := by
  unfold actB
  have hx : (x.1.1)ᵀ * ((x⁻¹ : d.G).1.1)ᵀ = 1 := by
    rw [← transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    simp
  calc _ = (mat g * mat g⁻¹) * v * ((x.1.1)ᵀ * ((x⁻¹ : d.G).1.1)ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = v := by rw [mat_mul_inv_k, hx, Matrix.one_mul, Matrix.mul_one]
theorem comm_schr_k (g : UA σ d.A.J) (x : d.G) : ∀ w, ∀ φ ∈ schA F d.κ,
    (d.om x⁻¹ * d.S g * d.om x * d.S g⁻¹) (schr d.B.ψ w φ) =
      schr d.B.ψ w ((d.om x⁻¹ * d.S g * d.om x * d.S g⁻¹) φ) := by
  intro w φ hφ
  obtain ⟨v, rfl⟩ := d.dd.e.surjective w
  have e1 : ∀ u, schr d.B.ψ (d.dd.e u) = d.dd.rho d.B.ψ u := fun u => rfl
  simp only [mul_apply_eq_comp, e1]
  have h1 := (hS_k d).impl g⁻¹ v φ hφ
  have hp1 := (hS_k d).pres g⁻¹ φ hφ
  have h2 := (hO_k d).impl x (mat g⁻¹ * v) _ hp1
  have hp2 := (hO_k d).pres x _ hp1
  have h3 := (hS_k d).impl g (actB (cA σ) x (mat g⁻¹ * v)) _ hp2
  have hp3 := (hS_k d).pres g _ hp2
  have h4 := (hO_k d).impl x⁻¹ (mat g * actB (cA σ) x (mat g⁻¹ * v)) _ hp3
  beta_reduce at h1 h3
  rw [h1, h2, h3, h4, actB_conj_k]
theorem exists_scalar_k (g : UA σ d.A.J) (x : d.G) :
    ∃ c : ℂ, ∀ φ ∈ schA F d.κ, (d.S g * d.om x * d.S g⁻¹) φ = c • d.om x φ := by
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSchUnique.scalar_of_commute d.B.ψ (std_k d) (d.om x⁻¹ * d.S g * d.om x * d.S g⁻¹)
    (fun l hl => by
      simp only [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
      exact (hS_k d).adm _ _ ((hO_k d).adm _ _ ((hS_k d).adm _ _ ((hO_k d).adm _ _ hl))))
    (comm_schr_k d g x)
  refine ⟨c, fun φ hφ => ?_⟩
  have h := congrArg (d.om x) (hc φ hφ)
  rw [map_smul] at h
  rw [← h]
  simp only [mul_apply_eq_comp]
  rw [← mul_apply_eq_comp (d.om x) (d.om x⁻¹), ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
end PositivityTheory.SiegelWeilFormula.tweyl
end
end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section
namespace PositivityTheory.SiegelWeilFormula.tweyl
variable (d : SD_k σ)
theorem detY_k : d.Y.J.det ≠ 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  intro h0
  have hd : (dbl d.Y.J).det = 0 := by
    rw [dbl, Matrix.det_fromBlocks_zero₁₂, h0, zero_mul]
  have h := congrArg Matrix.det hε
  rw [Matrix.det_mul, Matrix.det_mul, hd, mul_zero, zero_mul] at h
  exact det_weyl_block_ne_zero ε h.symm
theorem signY_k : ∃ ε : ℤˣ, ∀ i j, σ (d.Y.J j i) = ((ε : ℤ) : E) * d.Y.J i j := by
  rcases d.ok.sign with ⟨-, h⟩ | ⟨-, h⟩
  · exact ⟨-1, fun i j => by rw [h]; simp⟩
  · exact ⟨1, fun i j => by rw [h]; simp⟩
theorem exists_l_ne_k (hT : TBij_k) : ∃ φ ∈ schA F d.κ, d.l φ ≠ 0 := by
  obtain ⟨φz, hφz, hφz0⟩ := _root_.GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F d.κ
  have hne : d.T φz ≠ 0 := fun h => hφz0 (by rw [(hT F E σ d).2.2 φz hφz h]; rfl)
  obtain ⟨X, hX⟩ : ∃ X, d.T φz X ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  exact ⟨_, schr_mem_schA d.B.ψ (std_k d) _ φz hφz, hX⟩
end PositivityTheory.SiegelWeilFormula.tweyl
end
end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section
set_option linter.unusedSectionVars false
namespace PositivityTheory.SiegelWeilFormula.tweyl
variable (d : SD_k σ)
theorem comm_k (hT : TBij_k) (g : UA σ d.A.J) : ∀ Φ ∈ d.sch, ∀ x, d.om x (d.S g Φ) = d.S g (d.om x Φ) := by
  classical
  choose cf hcf using exists_scalar_k d g
  have hsp : ∀ y, ∀ φ ∈ schA F d.κ, d.om y φ ∈ schA F d.κ := fun y φ hφ => (hO_k d).pres y φ hφ
  have hinv : ∀ y (φ : d.Fn), d.om y (d.om y⁻¹ φ) = φ := fun y φ => by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  have hSinv : ∀ φ : d.Fn, d.S g⁻¹ (d.S g φ) = φ := fun φ => by
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
  have hSinv' : ∀ φ : d.Fn, d.S g (d.S g⁻¹ φ) = φ := fun φ => by
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  obtain ⟨φz, hφz, hφz0⟩ := _root_.GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F d.κ
  have huniq : ∀ y (c : ℂ), (∀ φ ∈ schA F d.κ, (d.S g * d.om y * d.S g⁻¹) φ = c • d.om y φ) → c = cf y :=
    fun y c hc => by
      have h1 := hc _ (hsp y⁻¹ φz hφz)
      rw [hcf y _ (hsp y⁻¹ φz hφz), hinv] at h1
      have h2 := congrFun h1 0
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      exact (mul_right_cancel₀ hφz0 h2).symm
  have hmul : ∀ y z, cf (y * z) = cf y * cf z := fun y z => (huniq (y * z) _ fun φ hφ => by
    have hR : (d.S g * d.om (y * z) * d.S g⁻¹) φ =
        (d.S g * d.om y * d.S g⁻¹) ((d.S g * d.om z * d.S g⁻¹) φ) := by
      simp only [mul_apply_eq_comp, map_mul, hSinv]
    rw [hR, hcf z φ hφ, map_smul, hcf y _ (hsp z φ hφ), smul_smul, map_mul, mul_apply_eq_comp, mul_comm]).symm
  have hone : cf 1 = 1 := (huniq 1 1 fun φ _ => by
    simp only [mul_apply_eq_comp, map_one, one_apply_eq_self, hSinv', one_smul]).symm
  let cM : d.G →* ℂ := { toFun := cf, map_one' := hone, map_mul' := hmul }
  let c := cM.toHomUnits
  have hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cf p := fun p => rfl
  have hcont_cf : Continuous cf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hφ := hsp p₀⁻¹ φz hφz
    have hf := (hO_k d).cont _ (GlobalTheory.WeilSchUnique.evalZero_mem_adelicSchwartzAdmittedForms d.κ) _ hφ
    have hh := (hO_k d).cont _ ((hS_k d).adm g _
        (GlobalTheory.WeilSchUnique.evalZero_mem_adelicSchwartzAdmittedForms d.κ)) _ ((hS_k d).pres g⁻¹ _ hφ)
    simp only [LinearMap.proj_apply, LinearMap.comp_apply] at hf hh
    have h0 : d.om p₀ (d.om p₀⁻¹ φz) 0 ≠ 0 := by rw [hinv]; exact hφz0
    refine (hh.continuousAt.div hf.continuousAt h0).congr ?_
    filter_upwards [hf.continuousAt.eventually_ne h0] with p hp
    show d.S g (d.om p (d.S g⁻¹ (d.om p₀⁻¹ φz))) 0 / d.om p (d.om p₀⁻¹ φz) 0 = cf p
    have e := hcf p _ hφ
    simp only [mul_apply_eq_comp] at e
    rw [e]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hcont : Continuous c := by
    refine Units.continuous_iff.2 ⟨hcont_cf, ?_⟩
    have : (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_cf.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero
  obtain ⟨φl, hφl, hl0⟩ := exists_l_ne_k d hT
  have hP : ∀ (p : d.G) (t : d.Gn),
      (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin d.n) = diagCols (Fin d.n) * t.1 → c p = 1 := fun p t hpt => by
    have K := hR_k d d.l d.ok.dbl.adm (fun z φ hφ => d.ok.dbl.kill z φ hφ) p t hpt
    have e1 := hcf p φl hφl
    have e2 := congrArg d.l e1
    simp only [mul_apply_eq_comp, map_smul, smul_eq_mul] at e2
    rw [d.ok.dbl.fix g _ (hsp p _ ((hS_k d).pres _ _ hφl)), K _ ((hS_k d).pres _ _ hφl), d.ok.dbl.fix g⁻¹ φl hφl,
      K φl hφl] at e2
    have hK := siegel_factor_ne (d.χ) (GeneralLinearGroup.det t) (adeleClass F).modu
      (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (GeneralLinearGroup.det t))
      ((Fintype.card (Fin d.m) : ℝ) / 2)
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    have hne := mul_ne_zero hK hl0
    rw [mul_assoc] at hne
    apply mul_right_cancel₀ hne
    rw [one_mul]
    simpa only [mul_assoc] using e2.symm
  obtain ⟨ε, hε⟩ := signY_k d
  have hc1 := _root_.GlobalTheory.SiegelChar.eq_one_of_siegel F E σ (cm_k d) d.n d.Y.J ε hε
      (detY_k d) c hcont hP
  intro Φ hΦ x
  have e := hcf x _ ((hS_k d).pres g Φ hΦ)
  have hcf1 : cf x = 1 := by rw [← hcv, hc1]; rfl
  rw [hcf1, one_smul] at e
  simp only [mul_apply_eq_comp, hSinv] at e
  exact e.symm
theorem tthetaComm_k (hT : TBij_k) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (d : SD_k σ), ∀ Φ ∈ d.sch, ∀ x g, d.om x (d.S g Φ) = d.S g (d.om x Φ) :=
  fun _ _ _ _ _ _ _ _ d Φ hΦ x g => comm_k d hT g Φ hΦ x
end PositivityTheory.SiegelWeilFormula.tweyl
end
end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section
namespace PositivityTheory.SiegelWeilFormula.Tpar
theorem frameData_k (d : SD_k σ) : ∃ t0 : GL (Fin d.n) E,
    incM F d.b.1 = fromCols (incM F d.b.1.toCols₁) (incM F d.b.1.toCols₂) ∧
    incM F d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) (AE F E)) * incM F t0.1 ∧
    ((diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) (AE F E)) * incM F t0.1)ᵀ * dbl (incM F d.Y.J) *
      (incM F d.b.1.toCols₂).map (cA σ) = 1 ∧
    incM F t0.1 * incM F (t0⁻¹).1 = 1 := by
  obtain ⟨t0, ht0'⟩ := d.ok.frame.2
  have ht0 : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) E) * t0.1 := ht0'
  have hBx : incM F d.b.1.toCols₁ =
      (diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) (AE F E)) * incM F t0.1 := by
    rw [ht0, TBij.incM_mul, incM_diagCols]
  refine ⟨t0, incM_fromCols _, hBx, ?_, ?_⟩
  · rw [← hBx]; exact frame_xy_A d.ok.frame
  · rw [← TBij.incM_mul, Units.mul_inv, incM_one]
theorem tPar_k : TPar_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, hB, hBx, hf, hT⟩ := frameData_k d
  have mem : ∀ w, d.dd.rho d.B.ψ w Φ ∈ schA F d.κ := fun w => schr_mem_schA _ hψ _ Φ hΦ
  refine ⟨fun x β hx X => ?_, fun x t u hx X => ?_, fun g X => ?_⟩
  · have h1 := inFrame_mul hx
    have h2 := inv_mul_frame h1 (N' := fromBlocks 1 (-β) 0 1)
      (by simp [fromBlocks_multiply, fromBlocks_one])
    rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
    replace h1 := Matrix.fromCols_inj h1
    replace h2 := Matrix.fromCols_inj h2
    rw [hBx] at h1 h2
    have hpar : IsPar x 1 := by
      have e := par_of hT (show mat2 x * ((diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) (AE F E)) *
          incM F t0.1) = (diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) (AE F E)) * incM F t0.1 * 1 by
        rw [h1.1]; simp)
      rw [Matrix.mul_one, hT] at e
      unfold IsPar
      rw [Units.val_one]
      exact e
    have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 x⁻¹)ᵀ = -(X * βᵀ * (incM F t0.1)ᵀ) *
        (diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) (AE F E))ᵀ + X * (incM F d.b.1.toCols₂)ᵀ := by
      rw [Matrix.mul_assoc, ← transpose_mul, h2.2]
      simp [transpose_mul, Matrix.transpose_add, Matrix.mul_add, Matrix.mul_assoc, Matrix.transpose_neg]
    simp only [SD_k.T, SD_k.tt, SD_k.gram]
    erw [l_rho_om h x _ hΦ, l_om_par h hpar (mem _), key, l_shift h hψ _ _ hΦ]
    have he := symp_N X β (incM F t0.1) (incM F d.b.1.toCols₂) (incM F d.A.J) (dbl (incM F d.Y.J)) hf
    dsimp only [incM, cA] at he
    dsimp only [incM, cA]
    rw [he]
    simp
  · have h1 := inFrame_mul hx
    have h2 := inv_mul_frame h1 (N' := fromBlocks (t⁻¹ : d.Gn).1 0 0 (u⁻¹ : GL (Fin d.n)
        (AE F E)).1)
      (by simp [fromBlocks_multiply, fromBlocks_one])
    rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
    replace h1 := Matrix.fromCols_inj h1
    replace h2 := Matrix.fromCols_inj h2
    rw [hBx] at h1 h2
    obtain ⟨G0, hG0⟩ : ∃ G0 : d.Gn, G0 = GeneralLinearGroup.map (inclR
        (AF F)) t0 :=
      ⟨_, rfl⟩
    have g1 : (G0 : d.Mn) = incM F t0.1 := by
      rw [hG0]; rfl
    have g2 : ((G0⁻¹ : d.Gn) : d.Mn) = incM F (t0⁻¹).1 := by
      rw [hG0, ← map_inv]; rfl
    have hpar : IsPar x (G0 * t * G0⁻¹) := by
      have e := par_of hT (show mat2 x * ((diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) (AE F E)) *
          incM F t0.1) = (diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) (AE F E)) * incM F t0.1 * t.1 by
        rw [h1.1]; simp)
      unfold IsPar
      rw [Units.val_mul, Units.val_mul, g1, g2]
      exact e
    have hdet : GeneralLinearGroup.det (G0 * t * G0⁻¹) = GeneralLinearGroup.det t := by
      rw [map_mul, map_mul, map_inv]
      exact mul_inv_cancel_comm _ _
    have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 x⁻¹)ᵀ = X * (u⁻¹).1ᵀ * (incM F d.b.1.toCols₂)ᵀ := by
      rw [Matrix.mul_assoc, ← transpose_mul, h2.2]
      simp [transpose_mul, Matrix.mul_assoc]
    simp only [SD_k.T]
    erw [l_rho_om h x _ hΦ, l_om_par h hpar (mem _), hdet, key]
  · simp only [SD_k.T]
    erw [l_rho_S h hψ g _ hΦ, Matrix.mul_assoc]; rfl
def TThetaSum_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E)
  (d : SD_k σ), ∀ Φ ∈ d.sch, HasSum (fun X : d.ME => d.T Φ (incM F X)) (thetaSum F Φ)
theorem tThetaSum_k : TThetaSum_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, ht0'⟩ := d.ok.frame.2
  have ht0 : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) E) * t0.1 := ht0'
  obtain ⟨Am, hAm⟩ : ∃ Am : Matrix d.N2 (Fin d.n) E, Am = Matrix.fromRows 1 (-1) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = (d.b⁻¹).1 * Am := ⟨_, rfl⟩
  have hA : Am = d.b.1.toCols₁ * M.toRows₁ + d.b.1.toCols₂ * M.toRows₂ := by
    rw [← Matrix.fromCols_mul_fromRows, Matrix.fromCols_toCols, Matrix.fromRows_toRows, hM, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]
  have hinj : ∀ v, M.toRows₂ *ᵥ v = 0 → v = 0 := by
    intro v hv
    have e1 : Am *ᵥ v = (diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) E) *ᵥ (t0.1 *ᵥ (M.toRows₁ *ᵥ v)) :=
        by
      rw [hA, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, add_zero, ht0,
        ← Matrix.mulVec_mulVec]
    funext i
    have a1 := congrFun e1 (Sum.inl i)
    have a2 := congrFun e1 (Sum.inr i)
    simp [hAm, diagCols, Matrix.fromRows_mulVec, Matrix.neg_mulVec] at a1 a2
    have : (2 : E) * v i = 0 := by linear_combination a1 - a2
    simpa using this
  have hu : IsUnit M.toRows₂.det := (Matrix.isUnit_iff_isUnit_det _).1
    (Matrix.mulVec_injective_iff_isUnit.1 fun v w e => sub_eq_zero.1 (hinj _ (by rw [Matrix.mulVec_sub, e, sub_self])))
  let e : d.ME ≃ d.ME :=
    { toFun := fun y => y * M.toRows₂ᵀ
      invFun := fun X => X * (M.toRows₂)⁻¹ᵀ
      left_inv := fun y => by
        simp only
        rw [Matrix.mul_assoc, ← transpose_mul, Matrix.nonsing_inv_mul _ hu, Matrix.transpose_one, Matrix.mul_one]
      right_inv := fun X => by
        simp only
        rw [Matrix.mul_assoc, ← transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one,
            Matrix.mul_one] }
  have hterm : ∀ y : d.ME,
      d.l (d.dd.rho d.B.ψ (incM F (fromCols y (-y))) Φ) = d.T Φ (incM F (e y)) := by
    intro y
    have hy : fromCols y (-y) = y * M.toRows₁ᵀ * t0.1ᵀ * (diagCols (Fin d.n) : Matrix d.N2
        (Fin d.n) E)ᵀ + y * M.toRows₂ᵀ * d.b.1.toCols₂ᵀ := by
      have : fromCols y (-y) = y * Amᵀ := by simp [hAm, Matrix.transpose_fromRows, Matrix.mul_fromCols]
      rw [this, hA, ht0]
      simp [Matrix.transpose_add, transpose_mul, Matrix.mul_add, Matrix.mul_assoc]
    have ea : incM F (y * M.toRows₁ᵀ * t0.1ᵀ * (diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) E)ᵀ) = incM F
        (y * M.toRows₁ᵀ * t0.1ᵀ) *
        (diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) (AE F E))ᵀ := by
      simp only [TBij.incM_mul, incM_transpose, incM_diagCols]
    have ec : incM F (y * M.toRows₂ᵀ * d.b.1.toCols₂ᵀ) = incM F (y * M.toRows₂ᵀ) * (incM F d.b.1.toCols₂)ᵀ := by
      simp only [TBij.incM_mul, incM_transpose]
    have hr := psi_rat h hψ (y * M.toRows₁ᵀ * t0.1ᵀ * (diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) E)ᵀ)
        (y * M.toRows₂ᵀ * d.b.1.toCols₂ᵀ)
    have ea' := ea
    have ec' := ec
    dsimp only [incM] at ea' ec'
    dsimp only [] at hr
    rw [ea', ec'] at hr
    rw [hy, incM_add, ea, ec]; erw [l_shift h hψ _ _ hΦ]
    dsimp only [incM, cA]
    rw [hr, one_mul]
    rfl
  have hs := h.theta Φ hΦ
  rw [show (fun y : d.ME => d.l (d.dd.rho d.B.ψ (incM F (fromCols y (-y))) Φ)) =
      (fun X => d.T Φ (incM F X)) ∘ e from funext hterm] at hs
  exact (Equiv.hasSum_iff e).1 hs
theorem tTheta_of_k
    (h2 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD_k σ),
      ∀ Φ ∈ d.sch, ∀ x g, d.om x (d.S g Φ) = d.S g (d.om x Φ)) : TTheta_k :=
  fun F E _ _ _ _ _ σ d Φ hΦ => ⟨tThetaSum_k F E σ d Φ hΦ, h2 F E σ d Φ hΦ⟩
end PositivityTheory.SiegelWeilFormula.Tpar
end

section
open GlobalTheory.RatWeilOp
namespace PositivityTheory.SiegelWeilFormula.Tunit
open TBij TBij.Adp
theorem exists_chart_k (d : SD_k σ) : ∃ (τ : d.κ ≃ TBij_k.Adp.Ix d)
    (d' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) d.κ),
    GlobalTheory.TowU.IsRat d' ∧ ∀ w, d'.e w = TBij_k.Adp.c0 d τ w := by
  classical
  have hD := d.ok.dbl
  let τ : d.κ ≃ TBij_k.Adp.Ix d := Fintype.equivOfCardEq (TBij_k.Adp.card_ix d)
  obtain ⟨a, ha, hact⟩ := exists_symp d.dd.e (TBij_k.Adp.c0 d τ) (fun w w' =>
      by rw [TBij_k.Adp.symplecticForm_coordinates, TBij_k.Adp.sy_eq]) (by
    rintro w ⟨y, z, h⟩
    obtain ⟨x, hx⟩ := rat_surj d.bs d.dd.e (fun x => hD.rat x) y z
    obtain rfl : w = incM F x := d.dd.e.injective (h.trans hx.symm)
    exact TBij_k.Adp.coordinates_rational d τ x)
  set J := jj d.κ F with hJ
  set b := -(J * aᵀ * J) with hb
  have hba : b * a = 1 := by
    rw [hb, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc aᵀ, ha, jj_mul_jj, neg_neg]
  have hab : a * b = 1 := mul_eq_one_comm.1 hba
  have hinv : ∀ w, act (b.map (algebraMap F (AF F))) (TBij_k.Adp.c0 d τ w) = d.dd.e w := fun w => by
    rw [hact w, ← act_mul, ← Matrix.map_mul, hba, Matrix.map_one _ (map_zero _) (map_one _), act_one']
  have hright : ∀ u, TBij_k.Adp.c0 d τ (d.dd.e.symm (act (b.map (algebraMap F (AF F))) u)) = u := fun u => by
    rw [hact, LinearEquiv.apply_symm_apply, ← act_mul, ← Matrix.map_mul, hab,
      Matrix.map_one _ (map_zero _) (map_one _), act_one']
  let e' : d.M2 ≃ₗ[AF F] (d.κ → AF F) × (d.κ → AF F) :=
    { TBij_k.Adp.c0 d τ with
      invFun := fun u => d.dd.e.symm (act (b.map (algebraMap F (AF F))) u)
      left_inv := fun w => by
        show d.dd.e.symm (act (b.map (algebraMap F (AF F))) (TBij_k.Adp.c0 d τ w)) = w
        rw [hinv, LinearEquiv.symm_apply_apply]
      right_inv := hright }
  refine ⟨τ, ⟨e', fun w w' => ?_⟩, fun x => ?_, fun w => rfl⟩
  · rw [d.dd.form]
    show om (d.dd.e w) (d.dd.e w') = om (TBij_k.Adp.c0 d τ w) (TBij_k.Adp.c0 d τ w')
    rw [TBij_k.Adp.symplecticForm_coordinates, TBij_k.Adp.sy_eq]
  · obtain ⟨y, z, h⟩ := TBij_k.Adp.coordinates_rational d τ x
    exact ⟨y, z, h⟩
theorem T_chart_k (d : SD_k σ) : ∃ (τ : d.κ ≃ TBij_k.Adp.Ix d) (S0 : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ))
    (S0' : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ)) (C : ℂ),
    GlobalTheory.TowU.IsOp d.B.ψ (fun w => TBij_k.Adp.c0 d τ (d.dd.e.symm w)) S0 S0' ∧
    ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S0 Φ (fun k => d.crd X (τ k)) := by
  have hψ := d.ok.good.std
  obtain ⟨τ, d', hrat, he'⟩ := exists_chart_k d
  obtain ⟨S0, S0', hS⟩ := _root_.GlobalTheory.TowU.darboux_change F E σ d.ok.good.cm d.B.ψ hψ
      (Fin d.m) d.N2 d.κ d.κ _ d.dd d'
    (by exact d.ok.dbl.rat) hrat
  have hop := hS.1
  have hs : (fun w => d'.e (d.dd.e.symm w)) = fun w => TBij_k.Adp.c0 d τ (d.dd.e.symm w) := funext fun w => he' _
  rw [hs] at hop
  have rhoS : ∀ w, ∀ φ ∈ schA F d.κ, S0 (d.dd.rho d.B.ψ w φ) = schr d.B.ψ (TBij_k.Adp.c0 d τ w) (S0 φ) := by
    intro w φ hφ
    simp only [Darboux.rho]
    rw [hop.Heisenberg₂ _ _ hφ, LinearEquiv.symm_apply_apply]
  have rhoS' : ∀ w, ∀ φ ∈ schA F d.κ, S0' (schr d.B.ψ (TBij_k.Adp.c0 d τ w) φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    intro w φ hφ
    have h1 := rhoS w (S0' φ) (hop.pres' φ hφ)
    rw [hop.right φ hφ] at h1
    have hm : d.dd.rho d.B.ψ w (S0' φ) ∈ schA F d.κ :=
      schr_mem_schA d.B.ψ hψ _ _ (hop.pres' φ hφ)
    rw [← h1, hop.left _ hm]
  set l' := d.l ∘ₗ S0' with hl'
  have hadm := hop.adm' d.l d.ok.dbl.adm
  have hinv : ∀ (y : d.κ → AF F), ∀ φ ∈ schA F d.κ, l' (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l' φ := by
    intro y φ hφ
    obtain ⟨w, hw⟩ : ∃ w, TBij_k.Adp.c0 d τ w = (0, y) := ⟨d'.e.symm (0, y), by rw [← he',
        LinearEquiv.apply_symm_apply]⟩
    obtain ⟨Z, rfl⟩ := TBij_k.Adp.coordinates_fst_eq_zero d τ w (by rw [hw])
    have e1 : (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = schr d.B.ψ (TBij_k.Adp.c0 d τ (Z * (TBij_k.Adp.dg d)ᵀ)) φ := by
      rw [hw]; funext x; simp [schr]
    rw [e1, hl', LinearMap.comp_apply, rhoS' _ φ hφ, LinearMap.comp_apply]
    exact d.ok.dbl.kill Z _ (hop.pres' φ hφ)
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CharInvForm.main F d.B.ψ hψ d.κ l' hadm hinv
  refine ⟨τ, S0, S0', c, hop, fun Φ hΦ X => ?_⟩
  have hΨ : d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ ∈ schA F d.κ :=
    schr_mem_schA d.B.ψ hψ _ _ hΦ
  have e0 :=
      TBij_k.Adp.coordinates_frame d τ X
  have e1 : d.T Φ X = l' (S0 (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ)) := by
    rw [hl', LinearMap.comp_apply, hop.left _ hΨ]
    rfl
  rw [e1, hc _ (hop.pres _ hΨ), rhoS _ _ hΦ, e0]
  simp [schr]
end PositivityTheory.SiegelWeilFormula.Tunit
end
end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace PositivityTheory.SiegelWeilFormula.Tunit
open Tpar
theorem tHeis_k : THeis_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ Z X
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, -, hBx, hf, -⟩ := Tpar.frameData_k d
  constructor
  · simp only [SD_k.T]
    erw [Tpar.rho_rho (A := d.A) (Y := d.Y) (dd := d.dd) (ψ := d.B.ψ) (X * (incM F d.b.1.toCols₂)ᵀ) (Z *
        (incM F d.b.1.toCols₂)ᵀ) Φ]; rw [map_smul, smul_eq_mul]
    change d.B.ψ (⅟2 * symp (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) _ _) * _ = _
    rw [symp_cols, frame_yy_A d.ok.frame, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.zero_mul, Matrix.trace_zero, neg_zero, map_zero, mul_zero, AddChar.map_zero_eq_one, one_mul,
          ← Matrix.add_mul]; rfl
  · simp only [SD_k.T, SD_k.tt, SD_k.gram]
    rw [hBx, transpose_mul, ← Matrix.mul_assoc]
    erw [Tpar.rho_rho (A := d.A) (Y := d.Y) (dd := d.dd) (ψ := d.B.ψ) (X * (incM F d.b.1.toCols₂)ᵀ) (Z *
        (incM F t0.1)ᵀ * (diagCols (Fin d.n))ᵀ) Φ]
    rw [map_smul, smul_eq_mul, add_comm]
    erw [l_shift h hψ _ _ hΦ]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    change ⅟2 * symp (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) _ _ + -(⅟2 * symp (cA σ) (-1) (incM F d.A.J) (dbl
        (incM F d.Y.J)) _ _) = _
    rw [darboux_anti d.dd, Matrix.mul_assoc Z, ← transpose_mul, symp_cols, hf, Matrix.mul_one, trace_gram,
      map_neg]
    linear_combination (Algebra.trace (AF F) (AE F E) (Matrix.trace (Z * (X.map (cA σ))ᵀ * (incM F d.A.J)ᵀ))) *
      (invOf_two_add_invOf_two : (⅟(2 : AF F) + ⅟2 = 1))
section
open TBij.Adp KTunit
local instance (priority := high)  {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] :
    MeasurableSpace (κ → AF F) := borel _
theorem tUnit_k : TUnit_k := by
  intro F E _ _ _ _ _ σ d ν hν x Φ hΦ Φ' hΦ'
  obtain ⟨τ, S0, S0', C, hop, hT⟩ := T_chart_k d
  have hpres : ∀ φ ∈ schA F d.κ, d.om x φ ∈ schA F d.κ := fun φ hφ => d.ok.dbl.weil.2.1.pres x φ hφ
  have hunit := d.ok.dbl.weil.2.1.unit
  obtain ⟨hμ, hint⟩ := KTunit.map_haar_k d τ ν hν
  set μ := ν.map (KTunit.cmap_k d τ) with hμdef
  have h1 : ∀ Ψ ∈ d.sch, ∀ Ψ' ∈ d.sch, ∫ X, d.T Ψ X * star (d.T Ψ' X) ∂ν =
      (C * star C) * ∫ y, S0 Ψ y * star (S0 Ψ' y) ∂μ := by
    intro Ψ hΨ Ψ' hΨ'
    rw [← integral_const_mul, ← hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hT _ hΨ, hT _ hΨ', star_mul']
    change _ = C * star C * (S0 Ψ (fun k => d.crd X (τ k)) * star (S0 Ψ' fun k => d.crd X (τ k)))
    ring
  rw [h1 _ (hpres Φ hΦ) _ (hpres Φ' hΦ'), h1 _ hΦ _ hΦ']
  congr 1
  obtain ⟨c, hc0, hctop, hcn⟩ := hop.norm μ μ hμ hμ
  have hp' : ∀ φ ∈ schA F d.κ, (S0 ∘ₗ d.om x ∘ₗ S0') φ ∈ schA F d.κ := fun φ hφ =>
    hop.pres _ (hpres _ (hop.pres' φ hφ))
  have hT' : ∀ φ ∈ schA F d.κ, ∫⁻ y, ‖(S0 ∘ₗ d.om x ∘ₗ S0') φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ := by
    intro φ hφ
    have e1 := hcn _ (hpres _ (hop.pres' φ hφ))
    have e2 := hcn _ (hop.pres' φ hφ)
    rw [hop.right φ hφ] at e2
    have e3 := hunit μ hμ x _ (hop.pres' φ hφ)
    simp only [LinearMap.comp_apply]
    rw [e1, e2, e3]
  have := GlobalTheory.DblUnitaryBox.integral_mul_star_eq μ hμ (S0 ∘ₗ d.om x ∘ₗ S0') hp' hT' (hop.pres Φ hΦ)
      (hop.pres Φ' hΦ')
  simpa only [LinearMap.comp_apply, hop.left _ hΦ, hop.left _ hΦ'] using this
end
end PositivityTheory.SiegelWeilFormula.Tunit
end

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section
namespace PositivityTheory.SiegelWeilFormula.TW
def Uniq_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d : SD_k σ), ∀ ν : Measure (d.MxE), ν.IsAddHaarMeasure →
  ∀ Λ : d.Fn →ₗ[ℂ] ℂ, Λ ∈ (adeleClass F).adm d.κ →
    (∀ Z : d.MxE, ∀ Φ ∈ d.sch, Λ (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₂)ᵀ) Φ) = Λ Φ) →
    ∃ C : ℂ, ∀ Φ ∈ d.sch, Λ Φ = C * ∫ Z, d.T Φ Z ∂ν
def UpTo_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d : SD_k σ), ∀ ν : Measure (d.MxE), ν.IsAddHaarMeasure → ∀ ε w, d.IsW ε w → ∃ C : ℂ, ∀ Φ ∈ d.sch,
  ∀ X, d.T (d.om w Φ) X = C * ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.T Φ Z ∂ν
def Poisson_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d : SD_k σ), ∀ ν, d.IsCov ν → ∀ ε : ℤˣ, ∀ f ∈ d.schM,
  ∑' X : d.ME, ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (incM F X) Z)) * f Z ∂ν =
    ∑' X : d.ME, f (incM F X)
def ThetaW_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d : SD_k σ), (∀ ε w, d.IsW ε w → ∀ Φ ∈ d.sch, d.om w Φ ∈ d.sch ∧ thetaSum F (d.om w Φ) = thetaSum F Φ) ∧
  ∃ Φ ∈ d.sch, thetaSum F Φ ≠ 0
theorem tWeyl_of_k (hB : TBij_k) (hT : TTheta_k) (h1 : UpTo_k) (h2 : Poisson_k) (h3 : ThetaW_k) : TWeyl_k := by
  intro F E _ _ _ _ _ σ d ν hν ε w hw Φ hΦ X
  obtain ⟨C, hC⟩ := h1 F E σ d ν hν.1 ε w hw
  obtain ⟨hθ, Φ₀, h0, hne⟩ := h3 F E σ d
  have e1 := (hT F E σ d _ (hθ ε w hw Φ₀ h0).1).1.tsum_eq
  have e2 := (hT F E σ d _ h0).1.tsum_eq
  have e3 := h2 F E σ d ν hν ε _ ((hB F E σ d).1 Φ₀ h0)
  simp only [hC Φ₀ h0] at e1
  rw [tsum_mul_left, e3, e2, (hθ ε w hw Φ₀ h0).2] at e1
  have : C = 1 := mul_right_cancel₀ hne (e1.trans (one_mul _).symm)
  rw [hC Φ hΦ X, this, one_mul]
end PositivityTheory.SiegelWeilFormula.TW

namespace PositivityTheory.SiegelWeilFormula.TW.ThetaWPf
theorem isW_rat_k (d : SD_k σ) {ε : ℤˣ} {w : d.G} (hw : d.IsW ε w) : w ∈ d.r2 := by
  refine kunf.rat_of_inFrame (b := d.b) (M := fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ?_
  rw [(hw : inFrame d.b w = _)]
  ext (i | i) (j | j) <;> simp [incM, Matrix.one_apply]; split_ifs <;> simp
theorem thetaW_k : TW.ThetaW_k := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun ε w hw Φ hΦ => ?_, GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F d.κ⟩
  exact ⟨d.ok.dbl.weil.2.1.pres w Φ hΦ, Tauto.thetaSum_rational_invariant d w (isW_rat_k d hw) Φ hΦ⟩
end PositivityTheory.SiegelWeilFormula.TW.ThetaWPf
end

section
namespace PositivityTheory.SiegelWeilFormula.TW.UpToPf
open Tpar
theorem w_cols_k (d : SD_k σ) {ε : ℤˣ} {w : d.G} (hw : d.IsW ε w) :
    mat2 w * incM F d.b.1.toCols₂ = incM F d.b.1.toCols₁ ∧
    mat2 w⁻¹ * incM F d.b.1.toCols₂ = ((ε : ℤ) : AE F E) • incM F d.b.1.toCols₁ := by
  obtain ⟨t0, hB, -, -, -⟩ := Tpar.frameData_k d
  have h1 := inFrame_mul hw
  have he : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hN : (fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 :
        d.Mn2) *
      fromBlocks 0 (((ε : ℤ) : AE F E) • 1) 1 0 = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    simp [smul_smul, he]
  have h2 := inv_mul_frame h1 hN
  rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
  obtain ⟨-, h1b⟩ := Matrix.fromCols_inj h1
  obtain ⟨-, h2b⟩ := Matrix.fromCols_inj h2
  refine ⟨?_, ?_⟩
  · rw [h1b]; simp
  · rw [h2b]; simp
theorem tt_smul_k (d : SD_k σ) (ε : ℤˣ) (X Z : d.MxE) :
    d.tt (d.gram (((ε : ℤ) : AE F E) • X) Z) = ((ε : ℤ) : AF F) * d.tt (d.gram X Z) := by
  simp only [SD_k.tt, SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul]
  rw [Int.cast_smul_eq_zsmul, map_zsmul, zsmul_eq_mul]
theorem upTo_of_k (hU : TW.Uniq_k) : TW.UpTo_k := by
  intro F E _ _ _ _ _ σ d ν hν ε w hw
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, -, hBx, -, -⟩ := Tpar.frameData_k d
  obtain ⟨hw1, hw2⟩ := w_cols_k d hw
  have hsp := h.weil.2.1.toIsSplitting
  obtain ⟨C, hC⟩ := hU F E σ d ν hν (d.l ∘ₗ d.om w) (hsp.adm w d.l h.adm) (by
    intro Z Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hsp.impl w _ Φ hΦ]
    have e : actB (cA σ) w (Z * (incM F d.b.1.toCols₂)ᵀ) =
        (Z * (incM F t0.1)ᵀ) * (diagCols (Fin d.n) : Matrix d.N2 (Fin d.n) (AE F E))ᵀ := by
      change Z * (incM F d.b.1.toCols₂)ᵀ * (mat2 w)ᵀ = _
      rw [Matrix.mul_assoc, ← transpose_mul, hw1, hBx, transpose_mul, Matrix.mul_assoc]
    rw [e]
    convert h.kill (Z * (incM F t0.1)ᵀ) _ (hsp.pres w Φ hΦ) using 4
    rfl)
  refine ⟨C, fun Φ hΦ X => ?_⟩
  change d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (d.om w Φ)) = _
  have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 w⁻¹)ᵀ =
      (((ε : ℤ) : AE F E) • X) * (incM F d.b.1.toCols₁)ᵀ := by
    rw [Matrix.mul_assoc, ← transpose_mul, hw2, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hr := l_rho_om h w (X * (incM F d.b.1.toCols₂)ᵀ) hΦ
  change d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (d.om w Φ)) =
    d.l (d.om w (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ * (mat2 w⁻¹)ᵀ) Φ)) at hr
  rw [hr, key]
  have hm : d.dd.rho d.B.ψ ((((ε : ℤ) : AE F E) • X) * (incM F d.b.1.toCols₁)ᵀ) Φ ∈ d.sch :=
    schr_mem_schA _ hψ _ Φ hΦ
  have e1 := hC _ hm
  simp only [LinearMap.comp_apply] at e1
  rw [e1]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  simp only
  rw [(Tunit.tHeis_k F E σ d Φ hΦ (((ε : ℤ) : AE F E) • X) Z).2, tt_smul_k]
end PositivityTheory.SiegelWeilFormula.TW.UpToPf
end
end
end
