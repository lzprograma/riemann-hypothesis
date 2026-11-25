module

public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilMeasdictHOfMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Unfold0K
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainEq
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacDataOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacLin
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.HolValueAtFinsum
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightC
public import Development.WeilBound.ThetaLifts.LatticeBasics.SecLaw
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.CompactStandardSubgroup.KCptPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.AddFDOfCover
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Exch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.RatVecCountable
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.AbsUnf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.AbsUnfB
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.CellsSub
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MemStabiliserIffFrameLowerBlock
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.TBlkEqTFMulProdTV
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
public import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.FrameInvPf
public import Development.WeilBound.ThetaLifts.LatticeBasics.ContinuousFlat

/-! # SiegelWeilKunfCells: Consolidated global theta-kernel definitions and proofs (SiegelWeilKunfCells). -/
@[expose] public section

noncomputable section
open UpperTheory.TP.W (GoodK)
open scoped TensorProduct NNReal Matrix Classical ComplexOrder SchwartzMap
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open Complex (exp)
open GlobalTheory.Eis (cosetSum term)
open GlobalTheory.Doubling (absE)
open Matrix (GeneralLinearGroup)
open Real (exp_pos)

namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace Act
def IndepDom_k : Prop := ForAllSD fun d => ∀ (L : LD_k d) s₁ f, IsSec d.K d.χ s₁ f → ∀ z : ℂ,
  (∀ nb lam 𝓖 𝓖₀, d.CD nb lam 𝓖 → d.CD nb lam 𝓖₀ →
    ∀ uM ν 𝓤 𝓤₀, L.UData uM ν 𝓤 → L.UData uM ν 𝓤₀ → ∀ T T', L.IsSub T T' → ∀ x,
      ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν =
        ∫ u in 𝓤₀, fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM u * x) ∂ν) ∧
  ∀ nb' lam' 𝓖' 𝓖'₀, CoefData (Y := L.Y) L.b nb' lam' 𝓖' → CoefData (Y := L.Y) L.b nb' lam' 𝓖'₀ →
    ∀ T' x, first_k L f s₁ z nb' lam' 𝓖' T' x = first_k L f s₁ z nb' lam' 𝓖'₀ T' x

def CptDom_k : Prop := ForAllSD fun d =>
  (∀ nb lam 𝓖, d.CD nb lam 𝓖 → ∃ 𝓖₀, d.CD nb lam 𝓖₀ ∧ IsCompact (closure 𝓖₀)) ∧
  ∀ L : LD_k d, ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∃ 𝓤₀, L.UData uM ν 𝓤₀ ∧ IsCompact (closure 𝓤₀)

def AbsConv_k : Prop := ForAllSD fun d => ∀ (L : LD_k d) s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ →
  ∃ t : ℝ, ∀ z : ℂ, t < z.re → ∀ nb lam 𝓖, d.CD nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ (T : d.nF_) (x : d.G),
    (∀ q : Cs_k d, Integrable (kq_k L f s₁ z nb T uM (rep_k q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖))) ∧
    Summable fun q : Cs_k d => ∫ p, ‖kq_k L f s₁ z nb T uM (rep_k q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))

def FirstEq_k : Prop := ForAllSD fun d => ∀ (L : LD_k d) s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ →
  ∃ t : ℝ, ∀ z : ℂ, t < z.re → ∀ nb lam 𝓖, d.CD nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ nb' lam' 𝓖', CoefData (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' → ∀ x,
    ∑' q : {q : Cs_k d // FirstOrbit L (rep_k q)}, tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep_k q.1) x =
      first_k L f s₁ z nb' lam' 𝓖' T' x

structure CLaw_k {d : SD_k σ} (R : RD_k d) (L : LD_k d) (w₁ : d.G) (cM : (Fin L.n → AE F E) × AF F → d.G)
    (κ : Measure ((Fin L.n → AE F E) × AF F)) : Prop where
  comm : ∀ w (τ : ℝ) (y : GR d.n) (g : G2 σ L.Y), IsDil (Pi.single L.i₀ 1) τ y → L.j g * R.ι w y = R.ι w y * L.j g
  wdil : ∀ w (τ : ℝ) (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y → ∃ p t, IsPar p t ∧
    (absE F E (GeneralLinearGroup.det t) : ℝ) = Real.exp (-(2 * τ)) ∧
    (d.χ (GeneralLinearGroup.det t) : ℂ) = 1 ∧ w₁ * R.ι w y = p * w₁
  cdil : ∀ w (τ : ℝ) (y : GR d.n), IsDil (Pi.single L.i₀ 1) τ y →
    ∃ sc : ((Fin L.n → AE F E) × AF F) ≃ᵐ ((Fin L.n → AE F E) × AF F), (∀ c, cM c * R.ι w y = R.ι w y * cM (sc c)) ∧
      κ.map sc = ENNReal.ofReal (Real.exp (2 * d.n * τ)) • κ

def SecUnf_k : Prop := ForAllSD fun {_ _ _ _ _ _ _ σ} d => ∀ (R : RD_k d) (L : LD_k d) s₁ f,
  IsSec d.K d.χ s₁ f → d.Eis f s₁ →
  ∃ t : ℝ, ∀ z : ℂ, t < z.re → ∀ nb lam 𝓖, d.CD nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∃ w₁ cM κ, CLaw_k R L w₁ cM κ ∧ ∃ K : ℂ, ∀ x,
    secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x = K * ∑' q' : Cs_k L.sd, ∫ β in 𝓖',
      (∫ c, phz_k d f s₁ z (w₁ * (cM c * (L.j (rep_k q' * nb' β) * x))) ∂κ) * d.B.ψ (-L.sd.tt (T'.1.1 * β.1)) ∂lam'

def SecLaw_k : Prop := ForAllSD fun {_ _ _ _ _ _ _ σ} d => ∀ (R : RD_k d) (L : LD_k d) s₁ f,
  IsSec d.K d.χ s₁ f → d.Eis f s₁ →
  ∃ t : ℝ, ∀ z : ℂ, t < z.re → ∀ nb lam 𝓖, d.CD nb lam 𝓖 → IsCompact (closure 𝓖) →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → IsCompact (closure 𝓤) → ∀ T T', L.IsSub T T' →
  ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' → IsCompact (closure 𝓖') →
  ∀ w (τ : ℝ) (y : GR d.n) x, IsDil (Pi.single L.i₀ 1) τ y →
    secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 (R.ι w y * x) = Complex.exp (τ * (d.n - 2 * z)) *
      secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x

theorem phz_par_k {d : SD_k σ} {f : d.G → ℂ} {s₁ : ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {τ : ℝ} {p : d.G}
    {t : GL (Fin d.n) (AE F E)} (hp : IsPar p t)
    (ha : (absE F E (GeneralLinearGroup.det t) : ℝ) = Real.exp (-(2 * τ)))
    (hχ : (d.χ (GeneralLinearGroup.det t) : ℂ) = 1) (g : d.G) :
    phz_k d f s₁ z (p * g) = exp (-(τ * (2 * z + d.n))) * phz_k d f s₁ z g := by
  have hH : ((d.Ht (p * g) : ℝ) : ℂ) = (Real.exp (-(2 * τ)) : ℂ) * ((d.Ht g : ℝ) : ℂ) := by
    simp only [SD_k.Ht]
    rw [d.ok.hgt.mul hp, ha, Real.toNNReal_mul (exp_pos _).le, NNReal.coe_mul, Real.coe_toNNReal _ (exp_pos _).le,
      Complex.ofReal_mul]
  have he (w : ℂ) : ((Real.exp (-(2 * τ)) : ℝ) : ℂ) ^ w = exp (-(2 * τ) * w) := by
    rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp] <;> push_cast <;> simp [Real.pi_pos, Real.pi_pos.le]
  unfold phz_k
  rw [hH, Complex.ofReal_mul_cpow (exp_pos _).le, hf.law p t g hp, hχ, ha, he, he, ← mul_assoc,
    show exp (-(τ * (2 * z + d.n))) = exp (-(2 * τ) * (z - s₁)) * exp (-(2 * τ) * (s₁ + d.n / 2)) by
      rw [← Complex.exp_add]; congr 1; ring]
  ring

theorem secLaw_of_k : SecUnf_k → SecLaw_k := by
  intro hU F E _ _ _ _ _ σ d R L s₁ f hf he
  obtain ⟨t, ht⟩ := hU F E σ d R L s₁ f hf he
  refine ⟨t, fun z hz nb lam 𝓖 hc hcG uM ν 𝓤 hUd hcU T T' hTT' nb' lam' 𝓖' hc' hcG' w τ y x hy => ?_⟩
  obtain ⟨w₁, cM, κ, hL, K, hK⟩ := ht z hz nb lam 𝓖 hc hcG uM ν 𝓤 hUd hcU T T' hTT' nb' lam' 𝓖' hc' hcG'
  obtain ⟨p, tp, hp, ha, hχ, hw⟩ := hL.wdil w τ y hy
  obtain ⟨sc, hsc, hκ⟩ := hL.cdil w τ y hy
  have key (h : G2 σ L.Y) : ∫ c, phz_k d f s₁ z (w₁ * (cM c * (L.j h * (R.ι w y * x)))) ∂κ =
      Complex.exp (τ * (d.n - 2 * z)) * ∫ c, phz_k d f s₁ z (w₁ * (cM c * (L.j h * x))) ∂κ := by
    have h1 (c : (Fin L.n → AE F E) × AF F) :
        w₁ * (cM c * (L.j h * (R.ι w y * x))) = p * (w₁ * (cM (sc c) * (L.j h * x))) := by
      rw [← mul_assoc (L.j h), hL.comm w τ y h hy, mul_assoc, ← mul_assoc (cM c), hsc c, mul_assoc, ← mul_assoc w₁, hw,
        mul_assoc]
    simp_rw [h1, phz_par_k hf z hp ha hχ]
    rw [integral_const_mul, ← integral_map_equiv sc (fun c => phz_k d f s₁ z (w₁ * (cM c * (L.j h * x)))), hκ,
      integral_smul_measure, ENNReal.toReal_ofReal (exp_pos _).le, Complex.real_smul, ← mul_assoc]
    congr 1; rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  rw [hK, hK]; simp_rw [key, mul_assoc (Complex.exp _), integral_const_mul]; rw [tsum_mul_left]; ring

theorem ctSplit_of_parts_k : IndepDom_k → CptDom_k → AbsConv_k → FirstEq_k → SecLaw_k → CTSplit_k := by
  intro hI hC hA hF hS F E _ _ _ _ _ σ d R L s₁ f hf he
  obtain ⟨tA, hA'⟩ := hA F E σ d L s₁ f hf he
  obtain ⟨tF, hF'⟩ := hF F E σ d L s₁ f hf he
  obtain ⟨tS, hS'⟩ := hS F E σ d R L s₁ f hf he
  refine ⟨max tA (max tF tS), fun z hz nb lam 𝓖 hc nb' lam' 𝓖' hc' uM ν 𝓤 hU T T' hTT' => ?_⟩
  obtain ⟨𝓖₀, hc₀, hk₀⟩ := (hC F E σ d).1 nb lam 𝓖 hc
  obtain ⟨𝓤₀, hU₀, hkU⟩ := (hC F E σ d).2 L uM ν 𝓤 hU
  obtain ⟨𝓖'₀, hc'₀, hk'₀⟩ := (hC F E σ L.sd).1 nb' lam' 𝓖' hc'
  refine ⟨secondOrbitSection L f s₁ z nb lam 𝓖₀ T uM ν 𝓤₀, fun x => ?_, fun w τ y x hy =>
    hS' z (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hz) nb lam 𝓖₀ hc₀ hk₀ uM ν 𝓤₀ hU₀ hkU
      T T' hTT' nb' lam' 𝓖'₀ hc'₀ hk'₀ w τ y x hy⟩
  obtain ⟨hi, hs⟩ := hA' z (lt_of_le_of_lt (le_max_left _ _) hz) nb lam 𝓖₀ hc₀ hk₀ uM ν 𝓤₀ hU₀ hkU T x
  have : Countable d.r2 := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (Cs_k d) := Quotient.countable
  have : IsFiniteMeasure (ν.restrict 𝓤₀) := isFiniteMeasure_restrict.2 (by simp [hU₀.2.2.2])
  have : IsFiniteMeasure (lam.restrict 𝓖₀) := isFiniteMeasure_restrict.2 (by simp [hc₀.2.2.2])
  obtain ⟨hsum, h2⟩ := exch (fun q : Cs_k d => kq_k L f s₁ z nb T uM (rep_k q) x) hi hs
  have e4 : ∫ u in 𝓤₀, fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM u * x) ∂ν =
      ∑' q : Cs_k d, tm_k L f s₁ z nb lam 𝓖₀ T uM ν 𝓤₀ (rep_k q) x := by
    refine Eq.trans ?_ h2
    refine integral_congr_ae (ae_of_all _ fun u => integral_congr_ae (ae_of_all _ fun β => ?_))
    simp only [SD_k.eis, cosetSum, term, kq_k, phz_k, rep_k]; rw [tsum_mul_right]; rfl
  change _ = first_k L f s₁ z nb' lam' 𝓖' T' x + _
  rw [(hI F E σ d L s₁ f hf z).1 nb lam 𝓖 𝓖₀ hc hc₀ uM ν 𝓤 𝓤₀ hU hU₀ T T' hTT' x,
    (hI F E σ d L s₁ f hf z).2 nb' lam' 𝓖' 𝓖'₀ hc' hc'₀ T' x,
    ← hF' z (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hz) nb lam 𝓖₀ hc₀ hk₀ nb' lam' 𝓖'₀ hc'₀ hk'₀
      uM ν 𝓤₀ hU₀ hkU T T' hTT' x,
    e4]
  exact (hsum.tsum_subtype_add_tsum_subtype_compl {q : Cs_k d | FirstOrbit L (rep_k q)}).symm
end Act

namespace kunf
variable {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E}

theorem sigma_invol_k (B : Base F E) (hB : GoodK σ B) (x : E) : σ (σ x) = x :=
  kfour.sigma_sigma_of_good_k hB x

private theorem cells_k (B : Base F E) (hB : GoodK σ B) (hb : IsFrame2 σ Y b) {ε : ℤˣ} {w : G2 σ Y}
    (hw : inFrame b w = Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0) {nb : nA σ Y b → G2 σ Y}
    (hnb : IsNMap b nb) (T : nF σ Y b) (hT : IsND T) (γ : G2 σ Y) (hγ : γ ∈ rat2 σ Y) :
    (∃ p ∈ par2 σ Y, p ∈ rat2 σ Y ∧ ∃ ν ∈ nF σ Y b, γ = p * (w * nb ν)) ∨
    (∃ β₀ : nA σ Y b, B.ψ (-(Algebra.trace (AF F) (AE F E) (T.1.1 * β₀.1).trace)) ≠ 1 ∧
      ∃ t, IsPar (γ * nb β₀ * γ⁻¹) t ∧ Matrix.GeneralLinearGroup.det t = 1) := by
  have hb0 := hb; obtain ⟨⟨ε₀, hε₀⟩, t₀, ht₀⟩ := hb
  have hs := sigma_invol_k B hB
  set e : E := ((ε₀ : ℤ) : E) with he_def
  have he : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hse : σ.toRingHom e = e := map_intCast _ _
  obtain ⟨M, hM, hMf⟩ := rat_frame hε₀ hγ
  obtain ⟨hMM', hM'M⟩ := _root_.PositivityTheory.SiegelWeilFormula.kunf.frame_inv_pf σ.toRingHom hs e he hse M hMf
  have hMi := inFrame_inv_of_rat hM hMM'
  by_cases hc : M.toBlocks₂₁.det ≠ 0
  · left
    have hblk : M.toBlocks₂₁ * (M.toBlocks₂₂.map σ.toRingHom)ᵀ +
        M.toBlocks₂₂ * (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) = 0 := by
      have h1 := congrArg Matrix.toBlocks₂₁ hMM'
      conv_lhs at h1 => rw [← Matrix.fromBlocks_toBlocks M]
      rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁] at h1
      simp only [Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂] at h1
      rw [h1]; ext i j; simp [Matrix.toBlocks₂₁]
    have hν := herm_quot σ.toRingHom he _ _ hc hblk
    set νE := M.toBlocks₂₁⁻¹ * M.toBlocks₂₂ with hνE
    have hνA : (incM F νE)ᵀ = -((((ε₀ : ℤ) : AE F E)) • (incM F νE).map (cA σ)) := by
      rw [← incM_transpose', hν, incM_map_cA]; ext i j; simp [incM, he_def]
    let ν : nA σ Y b := ⟨incM F νE, (mem_nA_iff hε₀ _).2 hνA⟩
    have hνF : ν ∈ nF σ Y b := mem_nF_iff.2 ⟨νE, rfl⟩
    have hwrat : w ∈ rat2 σ Y := rat_of_inFrame (M := jw n ((ε : ℤ) : E)) (by rw [hw, incM_jw, map_intCast]; rfl)
    refine ⟨γ * (w * nb ν)⁻¹, ?_, mul_mem hγ (inv_mem (mul_mem hwrat (nb_rat hnb hνF))), ν, hνF,
      by simp only [mul_assoc, inv_mul_cancel, mul_one]⟩
    rw [mem_stabiliser_iff_frame_lower_block hb0, mul_inv_rev, ← nb_neg hnb,
      GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hM, hnb,
      inFrame_w_inv hw, incM_toBlocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.toBlocks_fromBlocks₂₁]
    have hcd : incM F M.toBlocks₂₁ * incM F νE = incM F M.toBlocks₂₂ := by
      rw [← incM_mul', ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hc), Matrix.one_mul]
    show _ = 0; simp only [Matrix.mul_one, Matrix.mul_zero, zero_add]
    change incM F M.toBlocks₂₁ * -(incM F νE) + incM F M.toBlocks₂₂ = 0; rw [Matrix.mul_neg, hcd, neg_add_cancel]
  · right; push Not at hc
    obtain ⟨T', hT'⟩ := mem_nF_iff.1 T.2
    have hTh : T'ᵀ = -(e • T'.map σ.toRingHom) := by
      have h1 := (mem_nA_iff hε₀ T.1.1).1 T.1.2; rw [hT'] at h1
      apply incM_inj (F := F); rw [incM_transpose', h1, incM_map_cA]; ext i j; simp [incM, he_def]
    have hTd : T'.det ≠ 0 := fun h0 => hT (by
      show T.1.1.det = 0; rw [hT', incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])
    have hda : e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ * M.toBlocks₁₁ +
        (M.toBlocks₁₁.map σ.toRingHom)ᵀ * M.toBlocks₂₁ = 0 := by
      have h1 := congrArg Matrix.toBlocks₂₁ hM'M
      rw [toBlocks₂₁_mul', Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂] at h1
      rw [h1]; ext i j; simp [Matrix.toBlocks₂₁]
    obtain ⟨β₁, hβh, hcβ, ⟨v, w', hvw, hvw0⟩, htr⟩ :=
      _root_.PositivityTheory.SiegelWeilFormula.kunf.exists_beta_pf σ.toRingHom hs e he hse M.toBlocks₁₁ M.toBlocks₂₁ _ hc hda T' hTh hTd
    have hx0 : Algebra.trace F E (2 : E) ≠ 0 := by
      rw [show (2 : E) = algebraMap F E 2 from (map_ofNat (algebraMap F E) 2).symm, Algebra.trace_algebraMap,
        nsmul_eq_mul]
      exact mul_ne_zero (Nat.cast_ne_zero.2 Module.finrank_pos.ne') two_ne_zero
    obtain ⟨l, hl⟩ := _root_.PositivityTheory.SiegelWeilFormula.kunf.psi_moves_pf hB.std _ hx0
    set Λ : AE F E := algebraMap (AF F) (AE F E) l
    have hcΛ : cA σ Λ = Λ := (cA σ).commutes l
    have hβA : (Λ • incM F β₁)ᵀ = -((((ε₀ : ℤ) : AE F E)) • (Λ • incM F β₁).map (cA σ)) := by
      have hc' : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun _ => rfl
      rw [Matrix.transpose_smul, ← incM_transpose', hβh]; ext i j; simp [incM, he_def, hcΛ, hc']; ring
    let β₀ : nA σ Y b := ⟨Λ • incM F β₁, (mem_nA_iff hε₀ _).2 hβA⟩
    refine ⟨β₀, ?_, ?_⟩
    · have htt : Algebra.trace (AF F) (AE F E) (T.1.1 * β₀.1).trace =
          l * algebraMap F (AF F) (Algebra.trace F E 2) := by
        show Algebra.trace (AF F) (AE F E) (T.1.1 * (Λ • incM F β₁)).trace = _
        rw [hT', Matrix.mul_smul, Matrix.trace_smul, ← incM_mul', smul_eq_mul, ← Algebra.smul_def,
          LinearMap.map_smul, tt_rat, htr, smul_eq_mul]
      rwa [htt]
    · set Z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E := Matrix.fromBlocks 0 β₁ 0 0 with hZ
      set M' := Matrix.fromBlocks (M.toBlocks₂₂.map σ.toRingHom)ᵀ (e • (M.toBlocks₁₂.map σ.toRingHom)ᵀ)
        (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ) (M.toBlocks₁₁.map σ.toRingHom)ᵀ
      have hN : Matrix.fromBlocks 1 (β₀ : Matrix (Fin n) (Fin n) (AE F E)) 0 1 = 1 + Λ • incM F Z := by
        show Matrix.fromBlocks 1 (Λ • incM F β₁) 0 1 = _; ext (i | i) (j | j) <;> simp [hZ, incM, Matrix.one_apply]
      have h1 : incM F M * incM F M' = 1 := by rw [← incM_mul', hMM']; ext i j; simp [incM, Matrix.one_apply]
      have hX : M * Z * M' = Matrix.fromBlocks (M.toBlocks₁₁ * β₁ * (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ))
          (M.toBlocks₁₁ * β₁ * (M.toBlocks₁₁.map σ.toRingHom)ᵀ)
          (M.toBlocks₂₁ * β₁ * (e • (M.toBlocks₂₁.map σ.toRingHom)ᵀ))
          (M.toBlocks₂₁ * β₁ * (M.toBlocks₁₁.map σ.toRingHom)ᵀ) := by
        (conv_lhs => enter [1, 1]; rw [← Matrix.fromBlocks_toBlocks M]); rw [hZ, conj_blocks]
      have hP : inFrame b (γ * nb β₀ * γ⁻¹) = 1 + Λ • incM F (M * Z * M') := by
        rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hM, hnb,
          hMi, hN, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, h1, Matrix.mul_smul, Matrix.smul_mul, incM_mul',
          incM_mul']
      have h21 : (inFrame b (γ * nb β₀ * γ⁻¹)).toBlocks₂₁ = 0 := by
        rw [hP, hX, hcβ]; ext i j; simp [Matrix.toBlocks₂₁, incM]
      have h11 : (inFrame b (γ * nb β₀ * γ⁻¹)).toBlocks₁₁ = 1 + Λ • incM F (Matrix.vecMulVec v w') := by
        rw [hP, hX, hvw]; ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply, incM]
      obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 ((mem_stabiliser_iff_frame_lower_block hb0 _).2 h21)
      refine ⟨t, ht, Units.ext ?_⟩; show t.1.det = 1
      have hdet : (1 + Λ • incM F (Matrix.vecMulVec v w')).det = 1 := by
        rw [show Λ • incM F (Matrix.vecMulVec v w') =
          Matrix.vecMulVec (fun i => Λ * inclR (F := F) (AF F) (v i)) (fun j => inclR (F := F) (AF F) (w' j)) by
            ext i j; simp [incM, Matrix.vecMulVec_apply, mul_assoc]]
        refine det_one_add_rank_one _ _ (by
          rw [show (fun j => inclR (F := F) (AF F) (w' j)) ⬝ᵥ (fun i => Λ * inclR (F := F) (AF F) (v i)) =
            Λ * inclR (F := F) (AF F) (w' ⬝ᵥ v) by simp [dotProduct, Finset.mul_sum, map_sum, mul_left_comm],
            hvw0, map_zero, mul_zero])
      rw [((isPar_frame ht₀ _ t).1 ht).2, Matrix.det_mul, Matrix.det_mul, h11, hdet, mul_one, ← Matrix.det_mul,
        incM_GL_mul_inv, Matrix.det_one]

theorem a_pos_k (d : SD_k σ) (x : d.G) : 0 < d.a x := by
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x; rw [d.ok.hgt.val p t hp k hk]; exact _root_.GlobalTheory.ThK.Dbl.absE_pos _

theorem ht_eq_k (d : SD_k σ) (x : d.G) : ((d.Ht x : ℝ) : ℂ) = (d.a x : ℂ) := by
  simp only [SD_k.Ht, Real.coe_toNNReal _ (a_pos_k d x).le]

theorem continuous_a_k (d : SD_k σ) : Continuous d.a := by
  have hcl : IsClosed (par2 σ d.Y : Set d.G) := by
    rw [show (par2 σ d.Y : Set d.G) = (fun p : d.G => (inFrame d.b p).toBlocks₂₁) ⁻¹' {0} by
      ext p; exact _root_.PositivityTheory.SiegelWeilFormula.kunf.mem_stabiliser_iff_frame_lower_block d.ok.frame p]
    exact isClosed_singleton.preimage (continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame (σ := σ) (Y := d.Y) d.b).matrix_elem
        (Sum.inr i) (Sum.inl j))
  refine GlobalTheory.Doubling.continuous_of_prod (P := par2 σ d.Y) (K := d.K) hcl
    (GlobalTheory.CompanionTheory.StdK.isCompact_of_isStdK d.B d.ok.good.cm d.b d.K d.ok.stdK) (fun g => ?_) ?_
  · obtain ⟨p, t, hp, k, hk, e⟩ := d.ok.hgt.iwa g; exact ⟨⟨p, mem_parabolic_GL2_iff.2 ⟨t, hp⟩⟩, k, hk, e⟩
  · refine (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp
      (SecA.continuous_uDet.comp continuous_fst))).congr fun x => ?_
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 x.1.2
    dsimp only [Function.comp_apply]; rw [d.ok.hgt.val _ t ht _ x.2.2, SecA.uDet_eq ht]

theorem unfold_k : Unfold_k := by
  intro F E _ _ _ _ _ σ d s₁ f hf hE
  rcases hE 0 with ⟨_, _, _, t, -, -, -, -, -, -, -, hmaj⟩
  refine ⟨t, fun z hz nb lam 𝓖 hc ε w hw x => ?_⟩
  have hΦ : (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s₁) * f y) = GlobalTheory.ThK.Dbl.flat d.a f s₁ z :=
    funext fun _ => by rw [GlobalTheory.ThK.Dbl.flat, ht_eq_k]
  set φ := GlobalTheory.ThK.Dbl.flat d.a f s₁ z with hφ_def
  have hφ : Continuous φ := continuous_flat hf.cont (continuous_a_k d) (a_pos_k d) z
  have hlawF := Law.flat (s₀ := s₁) hf.law d.ok.hgt (a_pos_k d) z
  have hrat : ∀ p ∈ par2 σ d.Y, p ∈ d.r2 → ∀ y, φ (p * y) = φ y := fun p hp hr y => hlawF.rat d.ok.hecke hp hr y
  have hone : ∀ p t', IsPar p t' → GeneralLinearGroup.det t' = 1 → ∀ y, φ (p * y) = φ y :=
    fun p t' ht' hdet y => by rw [hφ_def, hlawF p t' y ht', hdet]; simp
  have hmaj' := (hmaj z hz).1; rw [hΦ] at hmaj'
  obtain ⟨hnb, hHaar, h𝓖, -⟩ := hc; have := hHaar
  have : Countable d.r2 := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (GlobalTheory.Eis.Cosets (par2 σ d.Y) d.r2) := Quotient.countable
  have hw_rat : w ∈ d.r2 := rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (by
    rw [hw]; ext (i | i) (j | j) <;> simp [incM, Matrix.one_apply]
    split_ifs <;> simp)
  have hLI : GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ d.Y ⊓ d.r2) φ := fun γ hγ g => hrat γ hγ.1 hγ.2 g
  let nbR : d.nF_ → d.r2 := fun ν => ⟨nb ν.1, nb_rat hnb ν.2⟩
  let act : GlobalTheory.Eis.Cosets (par2 σ d.Y) d.r2 → d.nF_ → GlobalTheory.Eis.Cosets (par2 σ d.Y) d.r2 :=
    fun q ν => GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q
  have hact0 (q) : act q 0 = q := by
    show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR 0) q = q
    rw [show nbR 0 = 1 from Subtype.ext (nb_zero hnb), GlobalTheory.AutomorphicL2Unitary.rmul_one]
  have hact (q ν ν') : act (act q ν) ν' = act q (ν + ν') := by
    show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν') (GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q) =
      GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR (ν + ν')) q
    rw [show nbR (ν + ν') = nbR ν * nbR ν' from Subtype.ext (nb_add hnb ν.1 ν'.1),
      GlobalTheory.AutomorphicL2Unitary.rmul_mul]
  let A : GlobalTheory.Eis.Cosets (par2 σ d.Y) d.r2 → d.nA_ → ℂ := fun q β => term (par2 σ d.Y) d.r2 φ (nb β * x) q
  have hA (q) : Continuous (A q) := hφ.comp (continuous_const.mul ((continuous_nb hnb).mul continuous_const))
  have hAmk (γ : d.r2) (β) : A (GlobalTheory.AutomorphicL2Unitary.mk _ γ) β = φ (γ.1 * (nb β * x)) :=
    GlobalTheory.Eis.term_mk hLI (nb β * x) γ
  have hAact (q ν β) : A (act q ν) β = A q (β + (ν : d.nA_)) := by
    have e : act q ν = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * nbR ν) := by
      show GlobalTheory.AutomorphicL2Unitary.rmul _ (nbR ν) q = _; (conv_lhs => rw [← Quotient.out_eq q]); rfl
    rw [e, hAmk]
    show φ ((q.out : d.r2).1 * nb ν.1 * (nb β * x)) = φ ((q.out : d.r2).1 * (nb (β + ν.1) * x))
    rw [nb_add hnb, nb_comm hnb β]; simp only [mul_assoc]
  obtain ⟨C, hC, hCx⟩ := kfour.nF_cocompact (kfour.sigma_sigma_of_good_k d.ok.good) d.ok.frame
  have hcov (β : d.nA_) : ∃ ν : d.nF_, β + (ν : d.nA_) ∈ C := by
    obtain ⟨γ, hγ, hγC⟩ := hCx β; exact ⟨⟨γ, hγ⟩, by rwa [add_comm]⟩
  obtain ⟨u, hu, hAu'⟩ := hmaj' ((fun β => nb β * x) '' C) (hC.image ((continuous_nb hnb).mul continuous_const))
  have hAu (q) (β) (hβ : β ∈ C) : ‖A q β‖ ≤ u q := hAu' _ ⟨β, hβ, rfl⟩ q
  let q₀ : GlobalTheory.Eis.Cosets (par2 σ d.Y) d.r2 := GlobalTheory.AutomorphicL2Unitary.mk _ ⟨w, hw_rat⟩
  have hinj : Function.Injective (act q₀) := fun ν ν' h => by
    obtain ⟨γ, hγ⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.1 h
    have hγ' : γ.1.1 * (w * nb ν.1) = w * nb ν'.1 := congrArg Subtype.val hγ
    have hP : (w * nb ν'.1) * (w * nb ν.1)⁻¹ ∈ par2 σ d.Y := by
      rw [← hγ', mul_inv_cancel_right]; exact Subgroup.mem_subgroupOf.1 γ.2
    exact (Subtype.ext (_root_.PositivityTheory.SiegelWeilFormula.kunf.big_inj' d.ok.frame hw hnb hP)).symm
  have hAq₀ (β) : A q₀ β = φ (w * nb β * x) := by rw [hAmk, mul_assoc]
  have hI := abs_integrable lam d.nF_ 𝓖 h𝓖 act hact0 hact A hA hAact C hC hcov u hu hAu q₀ hinj
  refine ⟨hI.congr (Filter.Eventually.of_forall hAq₀), fun T hT => ?_⟩
  let χ₀ : d.nA_ → ℂ := fun β => d.B.ψ (-d.tt (T.1.1 * β.1))
  have hχc : Continuous χ₀ := d.ok.good.std.1.comp (((IsModuleTopology.continuous_of_linearMap
    (Algebra.trace (AF F) (AE F E))).comp continuous_id.matrix_trace).comp
    (continuous_const.matrix_mul continuous_subtypeVal)).neg
  have hχadd (β β') : χ₀ (β + β') = χ₀ β * χ₀ β' := by
    simp only [χ₀, SD_k.tt, AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add (f := _), neg_add]
    exact AddChar.map_add_eq_mul _ _ _
  have hχΛ (ν : d.nF_) : χ₀ (ν : d.nA_) = 1 := by
    simp only [χ₀, SD_k.tt, AddChar.map_neg_eq_inv, psi_rat d.ok.good.std T ν, inv_one]
  have hsmall (q) (hq : ∀ ν, act q₀ ν ≠ q) : ∃ β₀, χ₀ β₀ ≠ 1 ∧ ∀ ν β, A (act q ν) (β + β₀) = A (act q ν) β := by
    rcases cells_k d.B d.ok.good d.ok.frame hw hnb T hT (q.out : d.r2).1 (q.out : d.r2).2 with
      ⟨p, hpP, hpΓ, ν, hνF, hγ⟩ | ⟨β₀, hψ, t', hpar, hdet⟩
    · exfalso; refine hq ⟨ν, hνF⟩ ?_; rw [← Quotient.out_eq q]
      exact GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨⟨p, hpΓ⟩, Subgroup.mem_subgroupOf.2 hpP⟩,
        Subtype.ext hγ.symm⟩
    · refine ⟨β₀, hψ, fun ν β => ?_⟩; rw [hAact, hAact]
      show φ ((q.out : d.r2).1 * (nb (β + β₀ + ν.1) * x)) = φ ((q.out : d.r2).1 * (nb (β + ν.1) * x))
      set γ := (q.out : d.r2).1
      rw [show γ * (nb (β + β₀ + ν.1) * x) = (γ * nb β₀ * γ⁻¹) * (γ * (nb (β + ν.1) * x)) by
        rw [show β + β₀ + ν.1 = β₀ + (β + ν.1) by abel, nb_add hnb]
        simp only [mul_assoc, inv_mul_cancel_left], hone _ t' hpar hdet]
  have heq := abs_unfold lam d.nF_ 𝓖 h𝓖 act hact0 hact A hA hAact χ₀ hχc hχadd hχΛ
    C hC hcov u hu hAu q₀ hinj hsmall
  show fc d.B.ψ d.b nb lam 𝓖 (cosetSum (par2 σ d.Y) d.r2 (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s₁) * f y)) T x = _
  rw [hΦ]
  show ∫ β in 𝓖, cosetSum (par2 σ d.Y) d.r2 φ (nb β * x) * χ₀ β ∂lam = ∫ β, φ (w * nb β * x) * χ₀ β ∂lam
  rw [show ∫ β in 𝓖, cosetSum (par2 σ d.Y) d.r2 φ (nb β * x) * χ₀ β ∂lam = ∫ β, A q₀ β * χ₀ β ∂lam from heq]
  exact integral_congr_ae (Filter.Eventually.of_forall fun β => by dsimp only; rw [hAq₀])
end kunf

namespace Act.ComplexParameterFamilyContinuity
def unipotentNilpotentPart {d : SD_k σ} (L : LD_k d) (u : Fin L.n → AE F E) : d.Mn :=
  ∑ j, Matrix.single L.i₀ (L.em j) (u j)

theorem em_ne_k {d : SD_k σ} (L : LD_k d) (j : Fin L.n) : L.em j ≠ L.i₀ := (L.rng (L.em j)).2 ⟨j, rfl⟩

theorem unipotent_nilpotent_mul_eq_zero {d : SD_k σ} (L : LD_k d) (u v : Fin L.n → AE F E) :
    unipotentNilpotentPart L u * unipotentNilpotentPart L v = 0 := by
  simp only [unipotentNilpotentPart, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ =>
    Matrix.single_mul_single_of_ne _ _ _ _ (em_ne_k L _) _

theorem continuous_unipotent_nilpotent {d : SD_k σ} (L : LD_k d) : Continuous (unipotentNilpotentPart L) :=
  continuous_finsetSum _ fun j _ => by
    rw [show (fun u : Fin L.n → AE F E => Matrix.single L.i₀ (L.em j) (u j)) =
      fun u => u j • Matrix.single L.i₀ (L.em j) (1 : AE F E) by
        funext u; rw [Matrix.smul_single, smul_eq_mul, mul_one]]
    exact (continuous_apply j).smul continuous_const

def muF_k {d : SD_k σ} (L : LD_k d) (u : Fin L.n → AE F E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  Matrix.fromBlocks (1 + unipotentNilpotentPart L u) 0 0 (((1 - unipotentNilpotentPart L u)ᵀ).map (cA σ))

private theorem one_add_mul_one_sub_k {d : SD_k σ} (L : LD_k d) (u : Fin L.n → AE F E) :
    (1 + unipotentNilpotentPart L u) * (1 - unipotentNilpotentPart L u) = 1 := by
  rw [mul_sub, mul_one, add_mul, one_mul, unipotent_nilpotent_mul_eq_zero, add_zero, add_sub_cancel_right]

theorem inFrame_uM_k {d : SD_k σ} (L : LD_k d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤)
    (u : Fin L.n → AE F E) : inFrame d.b (uM u) = muF_k L u := by
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame; obtain ⟨a', ha⟩ := h.1 u
  change inFrame d.b (uM u) = Matrix.fromBlocks (1 + unipotentNilpotentPart L u) 0 0 a' at ha
  have h12 := congrArg Matrix.toBlocks₁₂ (ha ▸ kunf.frame_eq hε (uM u))
  simp only [kunf.jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
    Matrix.transpose_zero, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.toBlocks_fromBlocks₁₂] at h12
  have e2 : a'.map (cA σ) = (1 - unipotentNilpotentPart L u)ᵀ := by
    calc a'.map (cA σ) = ((1 - unipotentNilpotentPart L u)ᵀ * (1 + unipotentNilpotentPart L u)ᵀ) * a'.map (cA σ) := by
          rw [← Matrix.transpose_mul, one_add_mul_one_sub_k, Matrix.transpose_one, Matrix.one_mul]
      _ = (1 - unipotentNilpotentPart L u)ᵀ := by rw [Matrix.mul_assoc, h12, Matrix.mul_one]
  rw [ha, show a' = ((1 - unipotentNilpotentPart L u)ᵀ).map (cA σ) by
    rw [← e2]; ext i j; simp [Matrix.map_apply, kfour.cA_cA' σ hσ]]; rfl

theorem continuous_uM_k {d : SD_k σ} (L : LD_k d) {uM : (Fin L.n → AE F E) → d.G} {ν 𝓤} (h : L.UData uM ν 𝓤) :
    Continuous uM := by
  have hN := continuous_unipotent_nilpotent L
  have hcA : Continuous fun M : d.Mn => M.map (cA σ) :=
    continuous_id.matrix_map (GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ)
  let muF' (u : Fin L.n → AE F E) :=
    Matrix.fromBlocks (1 - unipotentNilpotentPart L u) 0 0 (((1 + unipotentNilpotentPart L u)ᵀ).map (cA σ))
  have hmul (u : Fin L.n → AE F E) : muF_k L u * muF' u = 1 := by
    have e1 := one_add_mul_one_sub_k L u
    simp only [muF_k, muF', Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [e1, ← kunf.map_cA_mul, ← Matrix.transpose_mul, e1, Matrix.transpose_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.fromBlocks_one]
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine ((continuous_const.matrix_mul (Continuous.matrix_fromBlocks (continuous_const.add hN) continuous_const
        continuous_const (hcA.comp (continuous_const.sub hN).matrix_transpose))).matrix_mul continuous_const).congr
      fun u => by show _ = mat2 (uM u); rw [kunf.matrix_eq_inFrame_conj d.b, inFrame_uM_k L h]; rfl
  · refine ((continuous_const.matrix_mul (Continuous.matrix_fromBlocks (continuous_const.sub hN) continuous_const
        continuous_const (hcA.comp (continuous_const.add hN).matrix_transpose))).matrix_mul continuous_const).congr
      fun u => by
        show _ = mat2 (uM u)⁻¹
        rw [kunf.matrix_eq_inFrame_conj d.b, GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, inFrame_uM_k L h,
          Matrix.inv_eq_right_inv (hmul u)]; rfl

theorem continuous_phz_k (d : SD_k σ) {f : d.G → ℂ} (hf : Continuous f) (s₁ z : ℂ) : Continuous (phz_k d f s₁ z) := by
  have h1 : Continuous fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) := by
    rw [show (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁)) = fun x => ((d.a x : ℝ) : ℂ) ^ (z - s₁) from
      funext fun _ => by rw [kunf.ht_eq_k]]
    exact (Complex.continuous_ofReal.comp (kunf.continuous_a_k d)).cpow continuous_const
      (fun x => Complex.ofReal_mem_slitPlane.2 (kunf.a_pos_k d x))
  exact h1.mul hf
end Act.ComplexParameterFamilyContinuity

namespace Act
open ComplexParameterFamilyContinuity
theorem cptDom_k : CptDom_k := fun F E _ _ _ _ _ σ d => ⟨fun nb lam 𝓖 h => by
    have hσ := kfour.sigma_sigma_of_good_k d.ok.good; have := h.2.1
    obtain ⟨_, _, _, _⟩ := kfour.nA_top hσ d.ok.frame
    obtain ⟨K, hK, hc⟩ := kfour.nF_cocompact hσ d.ok.frame
    obtain ⟨𝓖₀, hfd₀, hcpt⟩ := addFD_of_cover' d.nF_ hK hc lam
    exact ⟨𝓖₀, ⟨h.1, h.2.1, hfd₀, by rw [← h.2.2.2]; exact hfd₀.measure_eq h.2.2.1⟩, hcpt⟩,
  fun L uM ν 𝓤 h => by
    have := h.2.1
    have : DiscreteTopology L.ratV := ratVec_discrete (F := F) (E := E) L.n
    have : Countable L.ratV := ratVec_countable (F := F) (E := E) L.n
    obtain ⟨K, hK, hc⟩ := ratVec_cocompact (F := F) (E := E) L.n
    obtain ⟨𝓤₀, hfd₀, hcpt⟩ := addFD_of_cover' L.ratV hK hc ν
    exact ⟨𝓤₀, ⟨h.1, h.2.1, hfd₀, by rw [← h.2.2.2]; exact hfd₀.measure_eq h.2.2.1⟩, hcpt⟩⟩

theorem absConv_k : AbsConv_k := by
  intro F E _ _ _ _ _ σ d L s₁ f hf he
  rcases he 0 with ⟨_, _, _, t, -, -, -, -, -, -, -, hmaj⟩
  refine ⟨t, fun z hz nb lam 𝓖 h𝓖 hc𝓖 uM ν 𝓤 h𝓤 hc𝓤 T x => ?_⟩
  obtain ⟨_, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  obtain ⟨_, _, _, _⟩ := kfour.nA_top (kfour.sigma_sigma_of_good_k d.ok.good) d.ok.frame
  have cu := continuous_uM_k L h𝓤; have cn := kunf.continuous_nb h𝓖.1; have cφ := continuous_phz_k d hf.cont s₁ z
  set m : (Fin L.n → AE F E) × d.nA_ → d.G := fun p => nb p.2 * (uM p.1 * x)
  have cm : Continuous m := (cn.comp continuous_snd).mul ((cu.comp continuous_fst).mul continuous_const)
  obtain ⟨u, hu, hub⟩ := (hmaj z hz).1 (m '' (closure 𝓤 ×ˢ closure 𝓖)) ((hc𝓤.prod hc𝓖).image cm)
  have cψ := kfour.continuous_chr (σ := σ) (Y := d.Y) (b := d.b)
    (GlobalTheory.StdCharWeilDatum.isCharAF d.ok.good.std).1 T.1.1
  obtain ⟨Mψ, hMψ⟩ := hc𝓖.exists_bound_of_continuousOn cψ.continuousOn
  set μ := (ν.restrict 𝓤).prod (lam.restrict 𝓖)
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by rw [h𝓤.2.2.2]; exact ENNReal.one_ne_top)
  have : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by rw [h𝓖.2.2.2]; exact ENNReal.one_ne_top)
  have hS : ∀ᵐ p ∂μ, p ∈ closure 𝓤 ×ˢ closure 𝓖 := by
    have hnull {α : Type} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] (ν' : Measure α) (S : Set α) :
        ν'.restrict S (closure S)ᶜ = 0 := by
      rw [Measure.restrict_apply isClosed_closure.measurableSet.compl,
        (Set.disjoint_left.2 fun _ (hy : _ ∈ (closure S)ᶜ) h' => hy (subset_closure h')).inter_eq, measure_empty]
    rw [ae_iff]
    refine measure_mono_null (t := (closure 𝓤)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (closure 𝓖)ᶜ)
      (fun p hp => by simp only [Set.mem_ofPred_eq, Set.mem_prod, not_and_or] at hp
                      exact hp.elim (fun h => .inl ⟨h, Set.mem_univ _⟩) (fun h => .inr ⟨Set.mem_univ _, h⟩))
      (measure_union_null (by rw [Measure.prod_prod, hnull, zero_mul]) (by rw [Measure.prod_prod, hnull, mul_zero]))
  have hbd (q : Cs_k d) : ∀ᵐ p ∂μ, ‖kq_k L f s₁ z nb T uM (rep_k q) x p‖ ≤ |u q| * |Mψ| := by
    filter_upwards [hS] with p hp; simp only [kq_k, norm_mul]
    exact mul_le_mul ((hub (m p) ⟨p, hp, rfl⟩ q).trans (le_abs_self _)) ((hMψ p.2 hp.2).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)
  have hint (q : Cs_k d) : Integrable (kq_k L f s₁ z nb T uM (rep_k q) x) μ :=
    Integrable.of_bound
      ((cφ.comp (continuous_const.mul cm)).mul (cψ.comp continuous_snd)).aestronglyMeasurable _ (hbd q)
  refine ⟨hint, Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun q => ?_)
    ((hu.abs.mul_right |Mψ|).mul_right (μ.real Set.univ))⟩
  calc ∫ p, ‖kq_k L f s₁ z nb T uM (rep_k q) x p‖ ∂μ ≤ ∫ _, |u q| * |Mψ| ∂μ :=
        integral_mono_ae (hint q).norm (integrable_const _) (hbd q)
    _ = |u q| * |Mψ| * μ.real Set.univ := by rw [integral_const, smul_eq_mul, mul_comm]
end Act

theorem Khead.secK_k : SecK_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ
  obtain ⟨c1, c2⟩ := sec_cont_law d.ok.dbl hΦ.1
  refine ⟨c1, fun p t x hp => by simp only [SD_k.sec0, s0]; exact c2 p t x hp, ?_⟩
  have := hΦ.2
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ)).map
    (LinearMap.pi fun x => d.l ∘ₗ d.om x)) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, funext fun x => by simp [SD_k.sec0, map_mul]⟩

namespace Atop

theorem LD.n_succ_k {d : SD_k σ} (L : LD_k d) : L.n + 1 = d.n := by
  have h1 : Finset.univ.image L.em = Finset.univ.erase L.i₀ := by
    ext i; simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    exact ((L.rng i).trans Set.mem_range).symm
  have h2 := congrArg Finset.card h1
  rw [Finset.card_image_of_injective _ L.inj, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at h2
  have := L.i₀.pos; omega

private def Tl (d : SD_k σ) : d.Fn →ₗ[ℂ] (d.MxE → ℂ) := ⟨⟨d.T, KFock.T_add_k d⟩, KFock.T_smul_k d⟩

private def secl (d : SD_k σ) : d.Fn →ₗ[ℂ] (d.G → ℂ) where
  toFun := d.sec0
  map_add' _ _ := funext fun _ => by simp only [SD_k.sec0, Pi.add_apply, map_add (f := _)]
  map_smul' _ _ := funext fun _ => by simp only [SD_k.sec0, Pi.smul_apply, map_smul, RingHom.id_apply]

theorem I_add (d : SD_k σ) (hT : TTheta_k) (hA : ThetaAuto_k) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch)
    (h' : Φ' ∈ d.sch) : d.I (Φ + Φ') = d.I Φ + d.I Φ' := by
  funext x
  have e : ∀ g, thetaSum F (d.om x (d.S g (Φ + Φ'))) =
      thetaSum F (d.om x (d.S g Φ)) + thetaSum F (d.om x (d.S g Φ')) := fun g => by
    rw [map_add (f := _), map_add (f := _)]
    have ha := d.ok.dbl.weil.2.1.pres x _ (d.ok.dbl.lin.pres g _ h)
    have hb := d.ok.dbl.weil.2.1.pres x _ (d.ok.dbl.lin.pres g _ h')
    have h3 := (hT F E σ d _ (d.sch.add_mem ha hb)).1
    rw [KFock.T_add_k] at h3
    exact h3.unique ((hT F E σ d _ ha).1.add (hT F E σ d _ hb).1)
  simp only [SD_k.I, thetaMean, Pi.add_apply, e]
  rw [average_eq, average_eq, average_eq, integral_add (((hA F E σ d).2.2 Φ h).1 x) (((hA F E σ d).2.2 Φ' h').1 x),
    smul_add]

theorem I_smul (d : SD_k σ) (hT : TTheta_k) (a : ℂ) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.I (a • Φ) = a • d.I Φ := by
  funext x
  have e : ∀ g, thetaSum F (d.om x (d.S g (a • Φ))) = a * thetaSum F (d.om x (d.S g Φ)) := fun g => by
    rw [map_smul, map_smul]
    have ha := d.ok.dbl.weil.2.1.pres x _ (d.ok.dbl.lin.pres g _ h)
    have h3 := (hT F E σ d _ (d.sch.smul_mem a ha)).1
    rw [KFock.T_smul_k] at h3
    exact h3.unique ((hT F E σ d _ ha).1.mul_left a)
  simp only [SD_k.I, thetaMean, Pi.smul_apply, e, smul_eq_mul]
  rw [average_eq, average_eq, integral_const_mul, mul_smul_comm]

theorem I_sum (d : SD_k σ) (hT : TTheta_k) (hA : ThetaAuto_k) {ι : Type} (s : Finset ι) (f : ι → d.Fn)
    (h : ∀ i ∈ s, f i ∈ d.sch) : d.I (∑ i ∈ s, f i) = ∑ i ∈ s, d.I (f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using I_smul d hT 0 d.sch.zero_mem
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, I_add d hT hA (h a (Finset.mem_insert_self _ _))
      (d.sch.sum_mem fun i hi => h i (Finset.mem_insert_of_mem hi)), ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

private def mkIl (c : ℂ) (d : SD_k σ) (hTT : TTheta_k) (hTA : ThetaAuto_k) {R : RD_k d} {w : InfinitePlace F}
    {Ψ : d.MxE → ℂ} {φ : PX d.m d.n →ₗ[ℂ] d.Fn} (hφ : R.IsLift w Ψ φ) : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) where
  toFun P := c • d.I (φ P)
  map_add' P Q := by rw [map_add (f := _), I_add d hTT hTA (hφ P).1 (hφ Q).1, smul_add]
  map_smul' a P := by rw [map_smul, I_smul d hTT a (hφ P).1, RingHom.id_apply, smul_comm]

private theorem mkGlobCore (c : ℂ) (hT : TAll_k) (hFM : FockMem_k) (hGS : GSplit_k) (hGI : GIinv_k) (hGD : GIdil_k)
    (hPK : PolyKFin_k) (d : SD_k σ) (hEA : d.EisAll) (R : RD_k d) (w : InfinitePlace F) {L : GR d.n → d.LF → d.LF}
    (hL : R.IsLocOp w L) {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n}
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
    {Ψ : d.MxE → ℂ} (hΨ : Ψ ∈ R.away w) {φ : PX d.m d.n →ₗ[ℂ] d.Fn} (hφ : R.IsLift w Ψ φ) :
    AbsSt.GlobCore (fun _ => true) (2 * Real.pi) sL ρ d.G d.p2 d.r2 (R.ι w) d.s₀ d.Ht
      ((secl d).comp φ) (mkIl c d hT.2.2.2.1 hT.2.2.2.2 hφ) := by
  obtain ⟨hTB, -, -, hTT, hTA⟩ := hT
  have hfock := (hFM F E σ d R).2.1 w Ψ hΨ
  have hKF : ∀ P, d.KFin (φ P) := fun P => hPK F E σ d R (φ P) (hφ P).1 (by rw [(hφ P).2]; exact hfock.1 P)
  have hom : ∀ k : GR d.n, InK (mR k) → ∀ P, d.om (R.ι w k) (φ P) = φ (ρ k P) := fun k hk P => by
    have h1 := (hL k (fP P) (KFock.isSw_fP P)).2 Ψ hfock.2 (φ P) (hφ P).1 (hφ P).2
    rw [hρ k P hk] at h1
    refine sub_eq_zero.mp ((hTB F E σ d).2.2 _ (d.sch.sub_mem (d.ok.dbl.weil.2.1.pres _ _ (hφ P).1) (hφ _).1) ?_)
    rw [show d.T (_ - _) = Tl d (_ - _) from rfl, map_sub]; change d.T _ - d.T _ = 0; rw [h1, (hφ _).2, sub_self]
  obtain ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ := hEA (φ 1) (hKF 1) d.s₀
  exact
    { ιcont := R.cont w
      split := fun g => by
        obtain ⟨x, y, c', r, hr, hg, hx⟩ := hGS F E σ d R w L hL Ψ hΨ φ hφ g
        exact ⟨x, y, c', r, hr, hg, fun y' => ⟨(hx y').1, fun P => by rw [hsL]; exact (hx y').2 P⟩⟩
      Icont := ((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.1.const_smul c
      Ileft := fun γ hγ g => congrArg (c * ·) (((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.2 γ hγ g)
      Ik := fun P g k hk => by
        show c * thetaMean d.om d.S d.μ d.D (φ P) (g * R.ι w k) = c * thetaMean d.om d.S d.μ d.D (φ (ρ k P)) g
        unfold thetaMean; simp only [map_mul, mul_apply_eq_comp, (hTT F E σ d (φ P) (hφ P).1).2, hom k hk P]
      Iinv := fun g a b P => by
        show c * d.I (φ (hOp (fun _ => true) (2 * Real.pi) a b P)) g = 0
        rw [hGI F E σ d R w Ψ hΨ φ hφ g a b P, mul_zero]
      Idil := fun g X a ha => by
        obtain ⟨U, H, hU, hR, hc, hH⟩ := hGD F E σ d R w Ψ hΨ φ hφ g X a ha
        refine ⟨U, fun y z => c * H y z, hU, hR, continuousOn_const.mul hc, fun y => ⟨(hH y).1.const_mul c,
          fun t => by show c * H y t = c * d.I (φ 1) (g * R.ι w (y * a t)); rw [(hH y).2.1 t],
          fun r => by
            show iteratedDeriv r (fun z => c * H y z) 0 = c * d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y)
            rw [iteratedDeriv_const_mul' c r (H y)]; show c * iteratedDeriv r (H y) 0 = _; rw [(hH y).2.2 r]⟩⟩
      eis := ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ }

private theorem ident_lincomb_k (hT : TAll_k) (d : SD_k σ) (hEA : d.EisAll) (c : ℂ) {k : ℕ} (a : Fin k → ℂ)
    (Ψ : Fin k → d.Fn) (hK : ∀ i, d.KFin (Ψ i))
    (hI : ∀ i x, HolValueAt (fun z => d.eis (d.sec0 (Ψ i)) d.s₀ z x) d.s₀ (c * d.I (Ψ i) x)) (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (∑ i, a i • Ψ i)) d.s₀ z x) d.s₀ (c * d.I (∑ i, a i • Ψ i) x) := by
  have hv : d.I (∑ i, a i • Ψ i) x = ∑ i, a i * d.I (Ψ i) x := by
    rw [I_sum d hT.2.2.2.1 hT.2.2.2.2 Finset.univ _ (fun i _ => d.sch.smul_mem _ (hK i).1), Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [I_smul d hT.2.2.2.1 (a i) (hK i).1]; rfl
  have hcc : ∀ i, ∃ t : ℝ, ∀ z : ℂ, t < z.re → GlobalTheory.Eis.CosetConv d.p2 d.r2
      (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - d.s₀) * d.sec0 (Ψ i) y) x := fun i => by
    obtain ⟨U, pp, Ê, t, -, -, -, -, -, -, -, hc⟩ := hEA _ (hK i) d.s₀
    refine ⟨t, fun z hz => ?_⟩
    obtain ⟨u, hu, hle⟩ := (hc z hz).1 {x} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hle x rfl q) hu
  choose tt htt using hcc
  have hsec : d.sec0 (∑ i, a i • Ψ i) = fun y => ∑ i, a i * d.sec0 (Ψ i) y := funext fun y => by
    rw [show d.sec0 _ = secl d _ from rfl, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
  have heq : EqRight (fun z => ∑ i, a i * d.eis (d.sec0 (Ψ i)) d.s₀ z x)
      (fun z => d.eis (d.sec0 (∑ i, a i • Ψ i)) d.s₀ z x) := by
    refine ⟨∑ i, |tt i|, fun z hz => ?_⟩
    have hz' : ∀ i, tt i < z.re := fun i => lt_of_le_of_lt
      ((le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (tt j)) (Finset.mem_univ i))) hz
    have hc' : ∀ i ∈ Finset.univ, GlobalTheory.Eis.CosetConv d.p2 d.r2
        (fun y => a i * (((d.Ht y : ℝ) : ℂ) ^ (z - d.s₀) * d.sec0 (Ψ i) y)) x := fun i _ =>
      (htt i z (hz' i)).of_norm_le (C := ‖a i‖) fun y => (norm_mul _ _).le
    have := KMain.cosetSum_finsum d.p2 d.r2 Finset.univ
      (fun i y => a i * (((d.Ht y : ℝ) : ℂ) ^ (z - d.s₀) * d.sec0 (Ψ i) y)) x hc'
    show ∑ i, a i * d.eis (d.sec0 (Ψ i)) d.s₀ z x = d.eis (d.sec0 (∑ i, a i • Ψ i)) d.s₀ z x
    rw [hsec]; unfold SD_k.eis
    rw [show (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - d.s₀) * ∑ i, a i * d.sec0 (Ψ i) y) =
        fun y => ∑ i, a i * (((d.Ht y : ℝ) : ℂ) ^ (z - d.s₀) * d.sec0 (Ψ i) y) from
      funext fun y => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring, this]
    exact Finset.sum_congr rfl fun i _ => (cosetSum_const_mul _ _ _ _ _).symm
  rw [hv, Finset.mul_sum, show ∑ i, c * (a i * d.I (Ψ i) x) = ∑ i, a i * (c * d.I (Ψ i) x) from
    Finset.sum_congr rfl fun _ _ => by ring]
  exact (KMain.holValueAt_finsum Finset.univ fun i _ => (holValueAt_const (a i) _).mul (hI i x)).congr heq

private theorem mainC_of_k (c : ℂ) (hA : AbsThm) (hT : TAll_k) (hTC : ThetaCoef_k) (hRD : RDEx_k)
    (hAux : SiegelWeilDatumProperties) (hFM : FockMem_k) (hLE : LiftEx_k) (hLo : LocOpEx_k) (hLI : LocInst_k)
    (hGS : GSplit_k) (hGI : GIinv_k) (hGD : GIdil_k) (hKP : KFinPoly_k) (hPK : PolyKFin_k) (hSK : SecK_k)
    (hLB : LamBd_k) (hLS : LamSing_k) (hU : Unfold_k) (d : SD_k σ) (hnm : d.n ≤ d.m) (hEA : d.EisAll)
    (hW : ∀ Φ, d.KFin Φ → WhitAt_k c d Φ) : MainC_k c d := by
  intro Φ hΦ x; obtain ⟨R⟩ := hRD F E σ d; obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨k, P, Ψ, hΨ, hsum⟩ := (hFM F E σ d R).2.2 w _ (hKP F E σ d R Φ hΦ)
  choose φ hφ using fun i => hLE F E σ d R w (Ψ i) (hΨ i)
  have hKi : ∀ i, d.KFin (φ i (P i)) := fun i =>
    hPK F E σ d R _ (hφ i (P i)).1 (by rw [(hφ i (P i)).2]; exact ((hFM F E σ d R).2.1 w (Ψ i) (hΨ i)).1 (P i))
  have hΦeq : Φ = ∑ i, (1 : ℂ) • φ i (P i) := by
    simp only [one_smul]
    refine sub_eq_zero.mp ((hT.1 F E σ d).2.2 _ (d.sch.sub_mem hΦ.1 (d.sch.sum_mem fun i _ => (hφ i (P i)).1)) ?_)
    rw [show d.T (_ - _) = Tl d (_ - _) from rfl, map_sub, map_sum]
    change d.T Φ - ∑ i, d.T (φ i (P i)) = 0; simp only [(hφ _ _).2, hsum, sub_self]
  rw [hΦeq]; refine ident_lincomb_k hT d hEA c (fun _ => 1) (fun i => φ i (P i)) hKi (fun i x' => ?_) x
  obtain ⟨L, hL⟩ := hLo F E σ d R w; obtain ⟨sL, ρ, p, q, e, hgood, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  obtain ⟨-, ⟨ε, ww, hww, -⟩, -⟩ := hAux F E σ d
  have hc := mkGlobCore c hT hFM hGS hGI hGD hPK d hEA R w hL hsL hρ (hΨ i) (hφ i)
  have hKF1 : d.KFin (φ i 1) := hPK F E σ d R _ (hφ i 1).1
    (by rw [(hφ i 1).2]; exact ((hFM F E σ d R).2.1 w (Ψ i) (hΨ i)).1 1)
  have hGDat : GlobData (fun _ => true) (2 * Real.pi) sL ρ d.G d.p2 d.r2 (R.ι w) d.s₀ d.Ht
      ((secl d).comp (φ i)) (mkIl c d hT.2.2.2.1 hT.2.2.2.2 (hφ i)) d.lamSet :=
    { ιcont := hc.ιcont, split := hc.split, Icont := hc.Icont, Ileft := hc.Ileft, Ik := hc.Ik, Iinv := hc.Iinv,
      Idil := hc.Idil, eis := hc.eis, Λadd := fun l hl => (hLB F E σ d l hl).1,
      Λbd := fun l hl => (hLB F E σ d l hl).2, Λsing := fun f hf hi hz => hLS F E σ d R w f hf hi hz,
      Λval := by
        rintro l ⟨nb, lam, 𝓖, T, x₀, hcd, hT', rfl⟩
        obtain ⟨t', ht'⟩ := hU F E σ d _ _ (hSK F E σ d _ hKF1) (hEA _ hKF1)
        show HolValueAt (fun z => fc d.B.ψ d.b nb lam 𝓖 (d.eis (d.sec0 (φ i 1)) d.s₀ z) T x₀) d.s₀
          (fc d.B.ψ d.b nb lam 𝓖 (c • d.I (φ i 1)) T x₀)
        rw [show fc d.B.ψ d.b nb lam 𝓖 (c • d.I (φ i 1)) T x₀ = c * fc d.B.ψ d.b nb lam 𝓖 (d.I (φ i 1)) T x₀ from by
          unfold fc; simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]; exact integral_const_mul c _,
          hTC F E σ d _ (hφ i 1).1 nb lam 𝓖 hcd T x₀]
        exact (hW _ hKF1 nb lam 𝓖 hcd ε ww hww T hT' x₀).congr
          ⟨t', fun z hz => ((ht' z hz nb lam 𝓖 hcd ε ww hww x₀).2 T hT').symm⟩ }
  exact hA d.m d.n (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ hLD (hgood hnm)
    d.G d.p2 d.r2 (R.ι w) d.s₀ d.Ht ((secl d).comp (φ i))
    (mkIl c d hT.2.2.2.1 hT.2.2.2.2 (hφ i)) d.lamSet hGDat (P i) x'

private theorem vacAllOfC (hG : AbsSt.GenCore) (hT : TAll_k) (hFM : FockMem_k) (hLE : LiftEx_k) (hLo : LocOpEx_k)
    (hLI : LocInst_k) (hGS : GSplit_k) (hGI : GIinv_k) (hGD : GIdil_k) (hKP : KFinPoly_k) (hPK : PolyKFin_k)
    (hSK : SecK_k) (hEW : EisWk_k) : VacAll_k := by
  intro F E _ _ _ _ _ σ d R c hV Φ hΦ x
  have hEA : d.EisAll := fun Ψ hΨ => hEW F E σ d _ _ (hSK F E σ d Ψ hΨ)
  let gens (s : Finset (InfinitePlace F)) : Set (d.MxE → ℂ) :=
    {f | ∃ (P : InfinitePlace F → PX d.m d.n) (g : d.Af3 → ℂ), (∀ w ∉ s, P w = 1) ∧ g ∈ SB _ ∧
      f = fun X => (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2}
  have claim : ∀ s : Finset (InfinitePlace F), ∀ Φ ∈ d.sch, d.T Φ ∈ Submodule.span ℂ (gens s) → ∀ x,
      HolValueAt (fun z => d.eis (d.sec0 Φ) d.s₀ z x) d.s₀ (c * d.I Φ x) := fun s => by
    induction s using Finset.induction_on with
    | empty =>
      refine fun Φ hΦ hTΦ x => hV Φ hΦ (Submodule.span_le.2 ?_ hTΦ) x
      rintro f ⟨P, g, hP, hg, rfl⟩
      exact Submodule.subset_span ⟨g, hg, funext fun X => by simp only [hP _ (Finset.notMem_empty _)]⟩
    | insert w s hw ih =>
      have hgen : ∀ f ∈ gens (insert w s), ∃ Φf : d.Fn, d.KFin Φf ∧ d.T Φf = f ∧ ∀ x,
          HolValueAt (fun z => d.eis (d.sec0 Φf) d.s₀ z x) d.s₀ (c * d.I Φf x) := by
        rintro f ⟨P, g, hP, hg, rfl⟩
        set Ψ : d.MxE → ℂ := fun X => (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) *
          g fun k => (d.crd X k).2 with hΨdef
        have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨P, g, hg, rfl⟩
        obtain ⟨φ, hφ⟩ := hLE F E σ d R w Ψ hΨ
        have hTP : ∀ Q : PX d.m d.n, d.T (φ Q) = fun X =>
            (∏ w', fP (Function.update P w Q w') (R.loc w' X)) * g fun k => (d.crd X k).2 := fun Q => by
          rw [(hφ Q).2]; funext X; simp only [RD_k.tens, hΨdef]
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, mul_assoc]
          congr 2; exact Finset.prod_congr rfl fun w' hw' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
        have hKF : ∀ Q, d.KFin (φ Q) := fun Q => hPK F E σ d R (φ Q) (hφ Q).1
          (by rw [hTP Q]; exact Submodule.subset_span ⟨_, g, hg, rfl⟩)
        have hvac : ∀ x, HolValueAt (fun z => d.eis (d.sec0 (φ 1)) d.s₀ z x) d.s₀ (c * d.I (φ 1) x) :=
          ih (φ 1) (hφ 1).1 (by
            rw [hTP 1]; refine Submodule.subset_span ⟨Function.update P w 1, g, fun w' hw' => ?_, hg, rfl⟩
            by_cases e : w' = w
            · subst e; exact Function.update_self _ _ _
            · rw [Function.update_of_ne e]; exact hP w' (by simp [e, hw']))
        obtain ⟨L, hL⟩ := hLo F E σ d R w; obtain ⟨sL, ρ, p, q, e, -, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
        have hCore := mkGlobCore c hT hFM hGS hGI hGD hPK d hEA R w hL hsL hρ hΨ hφ
        obtain ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, -, hconv⟩ := hEA (φ 1) (hKF 1) d.s₀
        obtain ⟨r, Fv, hr, hFc, hFd, hF0, hFv⟩ := vacData_of (fun z g => d.eis (d.sec0 (φ 1)) d.s₀ z g)
          d.s₀ (fun g => c * d.I (φ 1) g) U pp Ê t hUo hRD hs0 hp hhol hcont
          (fun z hz g => (hconv z hz).2 g) hvac
        refine ⟨φ (P w), hKF (P w), by rw [hTP (P w), Function.update_eq_self], fun x =>
          hG d.m d.n (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ hLD
            d.G d.p2 d.r2 (R.ι w) d.s₀ d.Ht ((secl d).comp φ)
            (mkIl c d hT.2.2.2.1 hT.2.2.2.2 hφ) hCore ⟨r, Fv, hr, hFc, hFd, hF0, hFv⟩ (P w) x⟩
      intro Φ hΦ hTΦ x; obtain ⟨k, a, f, hf⟩ := Submodule.mem_span_set'.1 hTΦ
      choose Φf hK hTf hI using fun i => hgen (f i).1 (f i).2
      have hΦeq : Φ = ∑ i, a i • Φf i := sub_eq_zero.mp ((hT.1 F E σ d).2.2 _
        (d.sch.sub_mem hΦ (d.sch.sum_mem fun i _ => d.sch.smul_mem _ (hK i).1)) (by
          rw [show d.T (_ - _) = Tl d (_ - _) from rfl, map_sub, map_sum]; simp only [map_smul]
          change d.T Φ - ∑ i, a i • d.T (Φf i) = 0; simp only [hTf, hf, sub_self]))
      rw [hΦeq]; exact ident_lincomb_k hT d hEA c a Φf hK hI x
  exact claim Finset.univ Φ hΦ.1 (Submodule.span_le.2 (by
    rintro f ⟨P, g, hg, rfl⟩; exact Submodule.subset_span ⟨P, g, fun _ hw => absurd (Finset.mem_univ _) hw, hg, rfl⟩)
    (hKP F E σ d R Φ hΦ)) x

private theorem mainLeOf (hRD : RDEx_k) (hLD : LDEx_k) (hVK : VacK_k) (hPK : PolyKFin_k) (hEq : MainEq_k)
    (hStep : Step_k) (hVA : VacAll_k) : MainLe_k := by
  intro F E _ _ _ _ _ σ d h
  have ind : ∀ k : ℕ, ∀ d : SD_k σ, d.m ≤ d.n → d.n - d.m = k → MainC_k 2 d := fun k => by
    induction k with
    | zero => exact fun d _ hk => hEq F E σ d (by omega)
    | succ k ih =>
      intro d _ hk
      have := d.ok.hm; obtain ⟨L⟩ := hLD F E σ d (by omega); have := LD.n_succ_k L
      obtain ⟨R⟩ := hRD F E σ d; obtain ⟨R'⟩ := hRD F E σ L.sd
      have hC' := ih L.sd (by show d.m ≤ L.n; omega) (by show L.n - d.m = k; omega)
      exact hVA F E σ d R 2 (hStep F E σ d R L R' (by omega) fun Φ hΦ hv x =>
        hC' Φ (hPK F E σ L.sd R' Φ hΦ ((hVK F E σ L.sd R').2.1 hv)) x)
  exact ind (d.n - d.m) d h rfl

theorem siegelWeilStd_of_k (hA : AbsThm) (hT : TAll_k) (hTC : ThetaCoef_k) (hLo : LocOpEx_k) (hLI : LocInst_k)
    (hGS : GSplit_k) (hGI : GIinv_k) (hGD : GIdil_k) (hKP : KFinPoly_k) (hPK : PolyKFin_k) (hU : Unfold_k)
    (hW : WhitK_k) (hWE : WhitEq_k) (hG : AbsSt.GenCore) (hLD : LDEx_k) (hVK : VacK_k) (hSt : Step_k) :
    SiegelWeilStd_k := by
  have hBL := _root_.PositivityTheory.RgEis.Hd.eisBL_k
  have hSK := Khead.secK_k; have hAux := kfour.auxiliaryExistence_holds
  have hRD := Krd.rdEx_k; have hFM := KFock.fockMem_k; have hLE := KFock.liftEx_k hT.1
  have hLB := kfour.lamBd_k; have hEW := Aeis.eisWk_k
  have hLS : LamSing_k := KSing.lamSing_of_k kfour.coefEx_k kfour.fourierZero_k Krd.denseW_k hAux
  have hMain : Main_k := fun F E _ _ _ _ _ σ d hnm hEA Φ hΦ x => by
    simpa only [one_mul] using mainC_of_k 1 hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU d
      hnm.le hEA (fun Φ' hΦ' nb lam 𝓖 hc ε ww hww T hT' x' => by
        simpa only [one_mul] using hW F E σ d hnm hEA Φ' hΦ' nb lam 𝓖 hc ε ww hww T hT' x') Φ hΦ x
  have hLt := Khead.headOf_k hBL hSK (Khead.eisStrong_of_k hBL) hMain
  have hEq : MainEq_k := fun F E _ _ _ _ _ σ d hmn => mainC_of_k 2 hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP
    hPK hSK hLB hLS hU d hmn.ge (fun Φ hΦ => hEW F E σ d _ _ (hSK F E σ d Φ hΦ)) (fun Φ hΦ => hWE F E σ d hmn Φ hΦ)
  have hLe := mainLeOf hRD hLD hVK hPK hEq hSt (vacAllOfC hG hT hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hEW)
  intro F E _ _ _ _ _ σ B m n A Y r s r' s' h1 h2 h3 h4 h5 χ h6 h7 κ _ dd om S l h8 b K a h9 h10 h11 μ D h12 h13 Φ h14
    h15
  by_cases hlt : n < m
  · simp only [ite_eq_left hlt, one_mul]
    exact hLt F E σ B m n A Y r s r' s' χ κ dd om S l b K a μ D Φ
      ⟨h1, h2, h3, hlt, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  · simp only [ite_eq_right hlt]
    let d : SD_k σ :=
      { B := B, m := m, n := n, A := A, Y := Y, r := r, s := s, χ := χ, κ := κ, dd := dd, om := om,
        S := S, l := l, b := b, K := K, a := a, μ := μ, D := D, bs := Khead.basis2_k h1,
        ok := ⟨h1, h2, h3, h4, h5.imp (fun h => ⟨h.1, h.2.skew⟩) (fun h => ⟨h.1, h.2.herm⟩),
          h6, h7, h8, h9, h10, h11, h12, h13⟩ }
    obtain ⟨Ê, ⟨t, hsum, -⟩, hw⟩ := hBL F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn
      (h5.elim (fun h => .inr h.2) (fun h => .inl h.2)) d.χ d.ok.hecke d.m d.ok.res d.b d.K d.a
      d.ok.frame d.ok.stdK d.ok.hgt d.s₀ (d.sec0 Φ) (hSK F E σ d Φ ⟨h14, h15⟩)
    intro x
    have hfl : ∀ z, (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - d.s₀) * d.sec0 Φ y) =
        GlobalTheory.ThK.Dbl.flat d.a (d.sec0 Φ) d.s₀ z := fun z => funext fun y => by
      simp only [SD_k.Ht, GlobalTheory.ThK.Dbl.flat]; rw [Real.coe_toNNReal _ (Khead.hgt_nonneg d.ok.hgt y)]
    have hmer := Khead.meromorphicOn_of_weak hw x
    have hext : IsExtAt (fun z => d.eis (d.sec0 Φ) d.s₀ z x) d.s₀ (Ê · x) :=
      ⟨Set.univ, trivial, isRightDomain_univ, hmer, t,
        fun z hz => by simp only [SD_k.eis, hfl z]; exact (hsum z hz x).tsum_eq.symm⟩
    obtain ⟨H', hext', han, hval⟩ := hLe F E σ d (not_lt.mp hlt) Φ ⟨h14, h15⟩ x
    have hloc : Function.update (Ê · x) d.s₀ (2 * d.I Φ x) =ᶠ[𝓝 d.s₀] H' := by
      filter_upwards [eventually_nhdsWithin_iff.1 (hext'.eventuallyEq hext)] with z hz
      by_cases e : z = d.s₀
      · subst e; rw [Function.update_self]; exact hval.symm
      · rw [Function.update_of_ne e]; exact (hz e).symm
    refine ⟨Function.update (Ê · x) d.s₀ (2 * d.I Φ x), fun z _ => (hmer z trivial).update _ _,
      ⟨max t d.s₀.re, fun z hz => ?_⟩, han.congr hloc.symm, Function.update_self _ _ _⟩
    rw [Function.update_of_ne (fun e => by subst e; exact lt_irrefl _ (lt_of_le_of_lt (le_max_right _ _) hz))]
    exact hsum z (lt_of_le_of_lt (le_max_left _ _) hz) x

end Atop
end PositivityTheory.SiegelWeilFormula
end
