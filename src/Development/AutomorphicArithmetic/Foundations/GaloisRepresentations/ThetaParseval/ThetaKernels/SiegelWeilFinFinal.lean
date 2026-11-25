module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFourierRealisesWeylElement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilThetadictAssemble
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCovolumeFormula
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleSpaceCovolumeFormula
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.SchwartzPolyGauss
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitP
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnipotentBorelTuples.TranslationInvariantFunctionalHaar
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.FrameLin
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.IntegralCovGen
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.RpSmulLeft
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.CovolUnique
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.DictAsm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Height
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.HolValueAtConstMulCpow
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.PureGenSubFock
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.RelAlg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.SdEx
public import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice
public import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
public import GroundTheory.AutomorphicForms.GL2.GJMatrixCoord
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetSqNormEqHermitianBlockFormula
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExistsAdelePiInf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.FinIndex
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HolomorphicTheta.HolomorphicAverageUniform
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacuumGeneratesPolynomials
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolLeadB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SplitB
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.VolImageMulVec
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

/-! # SiegelWeilFinFinal: Standard Siegel-Weil formula (`Fin.siegelWeilStd_k`) across split and non-split places. -/
@[expose] public section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula
open GlobalTheory.Doubling (absE)
set_option linter.style.haveILetI false
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace KWhit
open PositivityTheory.PfSWUS.Loc (trPair jtR)
open HeckeCharacterZeroLocus
private theorem meas_herm_top_loc (d : SD_k σ) : IsTopologicalAddGroup (SiegelWeilU.HermR (AF F) σ d.n) ∧
    LocallyCompactSpace (SiegelWeilU.HermR (AF F) σ d.n) ∧ SecondCountableTopology (SiegelWeilU.HermR (AF F) σ d.n) ∧
    BorelSpace (SiegelWeilU.HermR (AF F) σ d.n) ∧ Countable (MeasP.ratHerm F E σ d.n) := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, -, hcl, -⟩ :=
    GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ d.ok.good.cm (AF F)
  have : LocallyCompactSpace d.Mn := inferInstanceAs (LocallyCompactSpace (Fin d.n → Fin d.n → AE F E))
  have : SecondCountableTopology d.Mn := inferInstanceAs (SecondCountableTopology (Fin d.n → Fin d.n → AE F E))
  have : Countable E := _root_.Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableE
  have : Countable (Matrix (Fin d.n) (Fin d.n) E) := inferInstanceAs (Countable (Fin d.n → Fin d.n → E))
  refine ⟨inferInstance, (hcl d.n).locallyCompactSpace,
    inferInstanceAs (SecondCountableTopology ((SiegelWeilU.HermR (AF F) σ d.n : Set d.Mn))), ⟨rfl⟩, ?_⟩
  have := (Set.countable_range (AddMonoidHom.mapMatrix (SiegelWeilU.inclR (F := F) (E := E) (AF F)).toAddMonoidHom :
    Matrix (Fin d.n) (Fin d.n) E → d.Mn)).to_subtype
  exact Function.Injective.countable (f := fun x : MeasP.ratHerm F E σ d.n =>
    (⟨x.1.1, AddMonoidHom.mem_range.mp (AddSubgroup.mem_comap.mp x.2)⟩ : Set.range _)) fun _ _ h =>
    Subtype.ext (Subtype.ext (Subtype.mk.inj h))
private theorem meas_mx_top'_loc (d : SD_k σ) : IsTopologicalAddGroup d.MxE ∧ LocallyCompactSpace d.MxE ∧
    SecondCountableTopology d.MxE ∧ BorelSpace d.MxE ∧ Countable d.ratM := by
  obtain ⟨_, _, _, _⟩ := KFock.mxTop_k d
  have : Countable E := _root_.Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableE; have : Countable d.ME := inferInstanceAs (Countable (Fin d.m → Fin d.n → E))
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have hle : d.ratM ≤ (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom).range :=
    (AddSubgroup.closure_le _).mpr <| by rintro _ ⟨X, rfl⟩; exact ⟨X, rfl⟩
  have := (Set.countable_range (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom :
    d.ME → d.MxE)).to_subtype
  exact Function.Injective.countable (f := fun x : d.ratM =>
    (⟨x.1, AddMonoidHom.mem_range.mp (hle x.2)⟩ : Set.range _)) fun _ _ h => Subtype.ext (Subtype.mk.inj h)
private theorem T_finset_sum_loc (d : SD_k σ) {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (X : d.MxE) :
    d.T (∑ i ∈ s, c i • Φs i) X = ∑ i ∈ s, c i * d.T (Φs i) X := by
  induction s using Finset.cons_induction with
  | empty => simp [d.T_zero]
  | cons _ _ _ ih => rw [Finset.sum_cons, Finset.sum_cons, KK.W.T_add, KK.W.T_smul, ih]
namespace W
open PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.KWhit.Ht
private theorem cellFormula : CellFormula_k := fun hT F E _ _ _ _ _ σ d ν hν ε w hw Φ hΦ g x β hg => by
  have hx := d.om_sch x Φ hΦ
  rw [show d.sec0 Φ (w * g * x) = d.l (d.om w (d.om g (d.om x Φ))) by simp [SD_k.sec0, map_mul, mul_apply_eq_comp],
    ← KSplitP.T_zero_k d _, hT.2.2.1 F E σ d ν hν ε w hw _ (d.om_sch g _ hx) 0]
  refine integral_congr_ae (Eventually.of_forall fun Z => ?_)
  simp only [show d.gram 0 Z = 0 by simp [SD_k.gram], SD_k.tt, Matrix.trace_zero, map_zero, mul_zero,
    AddChar.map_zero_eq_one, one_mul]
  exact (hT.2.1 F E σ d _ hx).1 g β hg Z
private theorem coreX : CoreX_k :=
  fun ok vac c hT hA hS hU hW hD F E _ _ _ _ _ σ d R hok hE Φ hΦ P gf hpg hv x hx nb lam 𝓖 hcd ε w hw T hTnd =>
    match hD hT hA F E σ d R Φ hΦ P gf hpg x hx nb lam 𝓖 hcd ε w hw T hTnd with
    | ⟨dd, J, T', bs, ψ, θ, l, εs, fr, g, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c', C, hDat, hAn, ⟨e, he⟩, hC, ⟨t, ht⟩,
        μH, 𝓕, hH, hF, horb⟩ =>
      match hU F E σ d d.s₀ (d.sec0 Φ) (hS F E σ d Φ hΦ) (hE Φ hΦ) with
      | ⟨t', ht'⟩ => by
        have hG := hW F E σ d.m d.n dd J T' bs ψ (InfinitePlace F) θ l εs fr g P lv L₁ L₂ Φg Φf Φv μ ν hDat hok
          (Or.inr hAn) (fun h => ⟨fun i => congrFun (hv h) i, e, he⟩)
          ⟨max t t', fun z hz => (ht z (lt_of_le_of_lt (le_max_left _ _) hz)).1
            ((ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hcd ε w hw x).1)⟩ μH 𝓕 hH hF
        rw [horb, mul_left_comm]
        exact ((holValueAt_const_mul_cpow c' hC d.s₀).mul hG).congr ⟨t, fun z hz => ((ht z hz).2).symm⟩
section RelS
variable {d : SD_k σ} {R : RD_k d} {x : d.G} {t u : d.Gn} {T : d.nF_} {η : E} {T₀ : Matrix (Fin d.n) (Fin d.n) E}
  {hOf : d.nA_ → SiegelWeilU.HermR (AF F) σ d.n} {θ : InfinitePlace F → (InfiniteAdeleRing F ⊗[F] E →+* ℂ)}
  {fr : InfinitePlace F → d.Gmc} {g : InfinitePlace F → d.Gnc} (hR : Rel_k d R x t u T η T₀ hOf θ fr g)
include hR
private theorem real_at (ε : ℤˣ) (β : d.nA_) (D : d.Gn) {k : d.G} (hk : k ∈ d.K)
    (h1 : ((ε : ℤ) : AE F E) • t.1 = D.1 * (inFrame d.b k).toBlocks₂₁)
    (h2 : ((ε : ℤ) : AE F E) • (β.1 * u.1) = D.1 * (inFrame d.b k).toBlocks₂₂) (w : InfinitePlace F) :
    ‖piInf (d.B.emb w) D.1.det‖ ^ 2 = ‖piInf (d.B.emb w) t.1.det‖ ^ 2 *
      (1 + (((g w)⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w) * (((g w)⁻¹).1)ᴴ) *
        (((g w)⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w) * (((g w)⁻¹).1)ᴴ)).det.re := by
  set pw := piInf (d.B.emb w)
  have hcA (z : AE F E) : pw (cA σ z) = star (pw z) := by
    simp only [pw, piInf, RingHom.comp_apply, compInf_cA]; exact (infEmb_sigR d.ok.good.cm (d.B.emb w) _).symm
  have hK : ((inFrame d.b k).map pw).toBlocks₂₁ * (((inFrame d.b k).map pw).toBlocks₂₁)ᴴ +
      ((inFrame d.b k).map pw).toBlocks₂₂ * (((inFrame d.b k).map pw).toBlocks₂₂)ᴴ = 1 := Matrix.ext fun i j => by
    have := congrFun₂ (((d.ok.stdK k).1 hk).1 w) (Sum.inr i) (Sum.inr j)
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.conjTranspose_apply, Matrix.one_apply,
      Sum.inr.injEq] at this
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.add_apply] using this
  have hmap {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)) :
      (X * Y).map pw = X.map pw * Y.map pw := Matrix.map_mul
  have hsm {a b : Type} (c : AE F E) (X : Matrix a b (AE F E)) : (c • X).map pw = pw c • X.map pw := by ext _ _; simp
  have h1' := congrArg (fun M => M.map pw) h1; have h2' := congrArg (fun M => M.map pw) h2
  simp only [hsm, hmap, map_intCast] at h1' h2'
  have htu : (t.1.map pw)ᴴ * u.1.map pw = 1 := by
    have h0 := congrArg (fun M => M.map pw) (levi_tu_k d x t u hR.levi)
    simp only [hmap, Matrix.map_one _ (map_zero pw) (map_one pw)] at h0
    have h3 : ((t.1ᵀ.map pw) * ((u.1.map (cA σ)).map pw)).map (starRingEnd ℂ) =
        (1 : d.Mnc).map (starRingEnd ℂ) := by rw [h0]
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _),
      show ((u.1.map (cA σ)).map pw).map (starRingEnd ℂ) = u.1.map pw from by ext _ _; simp [hcA]] at h3
    rw [← h3]; rfl
  have hh : ((hOf β).1.map pw)ᴴ = (hOf β).1.map pw := Matrix.ext fun a b => by
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]; rw [← (hOf β).2 a b, sigR_eq_cA', hcA]
  have hβ : β.1.map pw = -(((d.B.emb w).1 η) • ((hOf β).1.map pw)ᵀ) := by
    rw [hR.hof β]; ext _ _
    simp [Matrix.map_apply, Matrix.mul_apply, Matrix.scalar_apply, incM, Matrix.diagonal_apply, pw, piInf, compInf,
      inclR, Algebra.TensorProduct.map_tmul, infEmb_tmul]
  have key := _root_.GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq (t.1.map pw) (u.1.map pw) (D.1.map pw)
    ((inFrame d.b k).map pw).toBlocks₂₁ ((inFrame d.b k).map pw).toBlocks₂₂ (β.1.map pw) ((hOf β).1.map pw) (g w).1
    ((ε : ℤ) : ℂ) ((d.B.emb w).1 η) (by rcases Int.units_eq_one_or ε with h | h <;> simp [h])
    ((map_ne_zero _).2 hR.ne) hK h1' h2' htu hh hβ (hR.gc w) ((Matrix.isUnit_iff_isUnit_det _).1 (g w).isUnit)
  rw [det_map, det_map] at key
  rw [show (Gen.matInf (hOf β).1).map (θ w) = ((hOf β).1.map pw).map star from by ext _ _; exact hR.th w _,
    Matrix.coe_units_inv]; exact key
private theorem fin_at (ε : ℤˣ) (β : d.nA_) (D : d.Gn) {k : d.G} (hk : k ∈ d.K)
    (h1 : ((ε : ℤ) : AE F E) • t.1 = D.1 * (inFrame d.b k).toBlocks₂₁)
    (h2 : ((ε : ℤ) : AE F E) • (β.1 * u.1) = D.1 * (inFrame d.b k).toBlocks₂₂) (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fin d.n → v.adicCompletion F ⊗[F] E)) [lam.IsAddHaarMeasure] :
    ‖Algebra.norm (v.adicCompletion F) (compFin F E v D.1.det)‖ =
      ‖Algebra.norm (v.adicCompletion F) (compFin F E v t.1.det)‖ *
        Gen.nu2 lam (L1 σ t v) (L2 σ u η v) (Gen.matV v (hOf β).1) := by
  set cf := compFin F E v
  have hmap {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)) :
      (X * Y).map cf = X.map cf * Y.map cf := Matrix.map_mul
  have hsm {a b : Type} (c : AE F E) (X : Matrix a b (AE F E)) : (c • X).map cf = cf c • X.map cf := by ext _ _; simp
  have htu : (t.1.map cf)ᵀ * (u.1.map cf).map (SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
    have h0 := congrArg (fun M => M.map cf) (levi_tu_k d x t u hR.levi)
    simp only [hmap, Matrix.map_one _ (map_zero cf) (map_one cf)] at h0
    rw [← h0, Matrix.transpose_map]; congr 1; ext _ _; exact (compFin_cA v _).symm
  have he1 : ‖Algebra.norm (v.adicCompletion F) (((ε : ℤ) : v.adicCompletion F ⊗[F] E))‖ = 1 := by
    rcases Int.units_eq_one_or ε with h | h; · simp [h]
    · rw [show (((ε : ℤ) : v.adicCompletion F ⊗[F] E)) = algebraMap (v.adicCompletion F) _ (-1) by
        rw [h]; simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, map_neg, map_one],
        Algebra.norm_algebraMap, norm_pow, norm_neg, norm_one, one_pow]
  have hβ : β.1.map cf = -((inclR (F := F) (v.adicCompletion F) η) • ((hOf β).1.map cf)ᵀ) := by
    rw [hR.hof β]; ext _ _
    simp [Matrix.map_apply, Matrix.mul_apply, Matrix.scalar_apply, incM, Matrix.diagonal_apply, cf, compFin_inclR]
  have hkk : (inFrame d.b k).map cf * (inFrame d.b k⁻¹).map cf = 1 := by
    rw [← hmap, ← d.inFrame_mul, mul_inv_cancel, d.inFrame_one, Matrix.map_one _ (map_zero cf) (map_one cf)]
  have hki (i j) : cf (inFrame d.b k i j) ∈ OE E v ∧ cf (inFrame d.b k⁻¹ i j) ∈ OE E v := by
    have h := ((d.ok.stdK k).1 hk).2
    have e (z : AE F E) : cf (finOne F • z) = cf z := by rw [compFin_smul, evFin_finOne, one_smul]
    exact ⟨e _ ▸ compFin_intHat v (h k (by simp) i j), e _ ▸ compFin_intHat v (h k⁻¹ (by simp) i j)⟩
  have h1' := congrArg (fun M => M.map cf) h1; have h2' := congrArg (fun M => M.map cf) h2
  simp only [hsm, hmap, map_intCast] at h1' h2'
  have key := HeightDict.fin_index d.ok.good.cm v d.n (t.1.map cf) (u.1.map cf) (D.1.map cf) (β.1.map cf)
    ((hOf β).1.map cf) (inclR (F := F) (v.adicCompletion F) η) (((ε : ℤ) : v.adicCompletion F ⊗[F] E))
    ((inFrame d.b k).map cf) ((inFrame d.b k⁻¹).map cf)
    (by rw [det_map]; exact t.det.isUnit.map cf) (by rw [det_map]; exact D.det.isUnit.map cf) htu
    ((Ne.isUnit hR.ne).map _) (ε.isUnit.map (Int.castRingHom _)) he1 hβ
    (fun a b => by simp only [Matrix.map_apply]; rw [← (hOf β).2 a b]; exact (compFin_sigR v _).symm)
    hkk (fun i j => (hki i j).1) (fun i j => (hki i j).2) h1' h2' lam
  rw [det_map, det_map] at key; exact key
private theorem asm_phase_cell (β : d.nA_) (Y : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    -(⅟(2 : AF F) * d.tt (β.1 * d.gram (toMx Y) (toMx Y))) =
      trPair (AF F) ((hOf β).1) (SiegelWeilU.gramR (AF F) σ (Jd_k d η) Y) := by
  have hg : SiegelWeilU.gramR (AF F) σ (Jd_k d η) Y =
      (SiegelWeilU.inclR (F := F) (AF F) η) • (d.gram (toMx Y) (toMx Y))ᵀ := Matrix.ext fun _ _ => by
    simp only [SiegelWeilU.gramR, SiegelWeilU.hR, SiegelWeilU.hform, SiegelWeilU.JR, Jd_k, Matrix.map_apply,
      Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, SD_k.gram, Matrix.mul_apply, toMx,
      Matrix.of_apply, incM, map_mul, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [asm_incl, asm_cA]; ring
  rw [trPair, hg, hR.hof β, SD_k.tt, asm_half, Matrix.neg_mul, asm_scalar_mul, Matrix.smul_mul, Matrix.trace_neg,
    Matrix.trace_smul, smul_eq_mul, map_neg, mul_neg, neg_neg]
  congr 2; simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
private theorem asm_phase_whit (β : d.nA_) :
    -d.tt (T.1.1 * β.1) = -trPair (AF F) ((Td η T₀).map (SiegelWeilU.inclR (AF F))) ((hOf β).1) := by
  rw [neg_inj, trPair, hR.hof β, hR.rat, SD_k.tt, asm_scalar_mul, Matrix.mul_neg, Matrix.mul_smul, Matrix.trace_neg,
    Matrix.trace_smul, smul_eq_mul, map_neg]
  have h2 : ∑ a, ∑ c, ((Td η T₀).map (SiegelWeilU.inclR (AF F))) a c * ((hOf β).1 : d.Mn) c a =
      algebraMap (AF F) (AE F E) (-2) * (SiegelWeilU.inclR (F := F) (AF F) η *
        (incM F T₀ * ((hOf β).1 : d.Mn)ᵀ).trace) := by
    simp only [Td, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_neg,
      map_ofNat, Matrix.trace, Matrix.diag, Matrix.mul_apply, incM, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
      rw [asm_incl, mul_assoc, mul_assoc, mul_left_comm (SiegelWeilU.inclR (AF F) η)]
  rw [h2, ← Algebra.smul_def (-2 : AF F) _, LinearMap.map_smul, smul_eq_mul, ← mul_assoc,
    show algebraMap F (AF F) (1 / 2) * (-2 : AF F) = -1 by
      rw [show (-2 : AF F) = algebraMap F (AF F) (-2) by rw [map_neg, map_ofNat], ← map_mul]; norm_num]; ring
end RelS
private theorem absE_split (d : SD_k σ) (x : (AE F E)ˣ) : ((absE F E x : ℝ≥0) : ℝ) =
    (∏ w, ‖piInf (d.B.emb w) x.1‖ ^ 2) * ∏ᶠ v, ‖Algebra.norm (v.adicCompletion F) (compFin F E v x.1)‖ := by
  rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]; congr 1
  · exact Finset.prod_congr rfl fun w _ => by
      rw [GlobalTheory.Doubling.absEw_eq_sq d.ok.good.cm (d.B.emb w), NNReal.coe_pow, coe_nnNorm]; rfl
  · set s := (GlobalTheory.Doubling.finite_mulSupport_absEv x).toFinset
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := s) (by simp [s]), NNReal.coe_prod,
      finprod_eq_prod_of_mulSupport_subset _ (s := s) fun v hv => by
        simp only [Set.Finite.coe_toFinset, s, Function.mem_mulSupport] at hv ⊢
        rw [normV_eq] at hv; exact fun h => hv (by rw [h, NNReal.coe_one])]
    exact Finset.prod_congr rfl fun v _ => (normV_eq x v).symm
private theorem heightDict : HeightDict_k := by
  intro F E _ _ _ _ _ σ d R x t u T η T₀ hOf θ fr g hR nb lam 𝓖 hc ε w hw
  choose lv hlv using fun v : HeightOneSpectrum (𝓞 F) => _root_.PositivityTheory.SiegelWeilFormula.HeightDict.exists_haar_tup (E := E) v d.n
  obtain ⟨hCO, hstd⟩ := HeightDict.fin_std_k (σ := σ) d d.n t u η hR.ne
  have hat : (0 : ℝ) < ((absE F E t.det : ℝ≥0) : ℝ) := Ht.absE_pos _
  refine ⟨lv, Ht.L1 σ t, Ht.L2 σ u η, ((absE F E t.det : ℝ≥0) : ℝ)⁻¹, inv_pos.2 hat, hlv, hCO, hstd, fun β => ?_⟩
  obtain ⟨D, k, hk, ha, hb1, hb2⟩ := Ht.frame_iwa_k d (w * nb β * x)
  obtain ⟨hr1, hr2⟩ := Ht.bottom_rows_k d x t u hR.levi nb hc.1 ε w hw β
  have h1 := hr1.symm.trans hb1; have h2 := hr2.symm.trans hb2
  have hre := fun w' => real_at hR ε β D hk h1 h2 w'; have hfi := fun v => fin_at hR ε β D hk h1 h2 v (lv v)
  set N : HeightOneSpectrum (𝓞 F) → ℝ := fun v => Gen.nu2 (lv v) (Ht.L1 σ t v) (Ht.L2 σ u η v) (Gen.matV v (hOf β).1)
  have hsD := absE_split d D.det; have hsT := absE_split d t.det
  have hfT := Ht.fin_supp t.det; have hfD := Ht.fin_supp D.det; have hT0 := Ht.normV_ne t.det
  simp only [Matrix.GeneralLinearGroup.val_det_apply] at hsD hsT hfT hfD hT0
  have hNs : (Function.mulSupport N).Finite := (hfD.union hfT).subset fun v hv => by
    by_contra hc'; simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hc'
    exact hv (by rw [show N v = ‖Algebra.norm (v.adicCompletion F) (compFin F E v D.1.det)‖ /
      ‖Algebra.norm (v.adicCompletion F) (compFin F E v t.1.det)‖ from by
        rw [hfi v, mul_div_cancel_left₀ _ (hT0 v)], hc'.1, hc'.2, div_one])
  have hA : ((absE F E D.det : ℝ≥0) : ℝ) =
      ((absE F E t.det : ℝ≥0) : ℝ) * Gen.nuA θ g lv (Ht.L1 σ t) (Ht.L2 σ u η) (hOf β).1 := by
    rw [hsD, hsT, show Gen.nuA θ g lv (Ht.L1 σ t) (Ht.L2 σ u η) (hOf β).1 =
      (∏ w', (1 + (((g w')⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w') * (((g w')⁻¹).1)ᴴ) *
        (((g w')⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w') * (((g w')⁻¹).1)ᴴ)).det.re) * ∏ᶠ v, N v from rfl,
      Finset.prod_congr rfl fun w' _ => hre w', Finset.prod_mul_distrib,
      finprod_congr fun v => hfi v, finprod_mul_distrib hfT hNs]; ring
  have hDpos := Ht.absE_pos D.det; rw [hA] at hDpos
  exact ⟨pos_of_mul_pos_right hDpos hat.le, by rw [ha, hA, mul_inv]⟩
private theorem measDict : MeasDict_k := by
  intro F E _ _ _ _ _ σ d R x t u T η T₀ hOf θ fr g hR
  have hchar := GlobalTheory.StdCharFromIsStd.isCharAF d.ok.good.std
  refine ⟨fun nb lam 𝓖 hc ν hν => ?_, fun μ νc hμ hνc => ?_⟩
  · obtain ⟨_, _, _, _, _⟩ := meas_herm_top_loc d
    obtain ⟨hemb, hH', hfd, h1⟩ := MeasD.meas_hOf_k hR hc; have := hν.1
    obtain ⟨𝓕, hF, hF1⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermCov.hermCovol F E σ d.ok.good.cm d.B.ψ hchar d.n ν hν
    exact ⟨hemb, hemb.measurable,
      @MeasG.covol_unique _ _ _ _ _ _ _ _ (MeasP.ratHerm F E σ d.n) _ _ _ hν.1 hH' _ _ hF hfd hF1 h1⟩
  · obtain ⟨_, _, _, _, _⟩ := meas_mx_top'_loc d
    have hND : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (Jd_k d η) :=
      ⟨fun i j => hR.herm j i, by rw [Jd_k, Matrix.det_transpose, Matrix.det_smul]
                                  exact mul_ne_zero (pow_ne_zero _ hR.ne) (meas_detA_k d)⟩
    obtain ⟨𝓕, hF, hF1⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.TupCovolume.tupCovol F E σ d.ok.good.cm d.m (Jd_k d η) hND
      d.B.ψ hchar d.n μ hμ
    obtain ⟨hemb, hH', hfd, h1⟩ := MeasD.meas_toMx_k d μ 𝓕 hμ.1 hF hF1
    obtain ⟨hνH, 𝓖, hG, hG1⟩ := hνc
    exact ⟨hemb, hemb.measurable, @MeasG.covol_unique _ _ _ _ _ _ _ _ d.ratM _ _ _ hνH hH' _ _ hG hfd hG1 h1⟩
private def genF {d : SD_k σ} (R : RD_k d) (P : InfinitePlace F → PX d.m d.n) (g : d.Af3 → ℂ) (X : d.MxE) : ℂ :=
  (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2
private theorem span_lift {d : SD_k σ} (R : RD_k d)
    (hB : (∀ Φ ∈ d.sch, d.T Φ ∈ d.schM) ∧ (∀ f ∈ d.schM, ∃ Φ ∈ d.sch, d.T Φ = f) ∧ (∀ Φ ∈ d.sch, d.T Φ = 0 → Φ = 0))
    (hF : R.fock ≤ d.schM) (S : Submodule ℂ d.MF) (p : (InfinitePlace F → PX d.m d.n) → Prop)
    (hS : S ≤ Submodule.span ℂ {f | ∃ P g, p P ∧ g ∈ SB _ ∧ f = genF R P g})
    (hgen : ∀ P φ, p P → Dense.Good φ → genF R P (Dense.pf φ) ∈ R.fock) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hTΦ : d.T Φ ∈ S) :
    ∃ (k : ℕ) (c : Fin k → ℂ) (Φs : Fin k → d.Fn),
      (∀ i, Φs i ∈ d.sch ∧ ∃ P φ, p P ∧ Dense.Good φ ∧ d.T (Φs i) = genF R P (Dense.pf φ)) ∧ Φ = ∑ i, c i • Φs i := by
  set G : Set d.MF := {f | ∃ P φ, p P ∧ Dense.Good φ ∧ f = genF R P (Dense.pf φ)}
  let genL (P : InfinitePlace F → PX d.m d.n) : (d.Af3 → ℂ) →ₗ[ℂ] d.MF :=
    ⟨⟨genF R P, fun _ _ => funext fun _ => by simp only [genF, Pi.add_apply]; ring⟩,
     fun _ _ => funext fun _ => by simp only [genF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring⟩
  have hle : S ≤ Submodule.span ℂ G := hS.trans <| Submodule.span_le.2 fun _ ⟨P, g, hp, hg, hEq⟩ => by
    subst hEq; change genL P g ∈ Submodule.span ℂ G
    exact Submodule.span_induction (fun _ ⟨φ, hφ, e⟩ => e ▸ Submodule.subset_span ⟨P, φ, hp, hφ, rfl⟩)
      (by rw [map_zero]; exact zero_mem _) (fun _ _ _ _ hx hy => by rw [map_add]; exact add_mem hx hy)
      (fun _ _ _ hx => by rw [map_smul]; exact Submodule.smul_mem _ _ hx) (Dense.mem_span_pf hg)
  obtain ⟨k, c, gs, hsum⟩ := Submodule.mem_span_set'.1 (hle hTΦ)
  choose Φs hΦs hTs using fun i : Fin k => let ⟨P, φ, hp, hφ, e⟩ := (gs i).2; hB.2.1 _ (hF (e ▸ hgen P φ hp hφ))
  refine ⟨k, c, Φs, fun i => ⟨hΦs i, let ⟨P, φ, hp, hφ, e⟩ := (gs i).2; ⟨P, φ, hp, hφ, (hTs i).trans e⟩⟩, ?_⟩
  refine sub_eq_zero.1 (hB.2.2 _ (sub_mem hΦ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΦs i)))
    (funext fun X => ?_))
  change (d.l ∘ₗ schrL d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ))) (Φ - ∑ i, c i • Φs i) = 0
  rw [map_sub]; change d.T Φ X - d.T (∑ i, c i • Φs i) X = 0; rw [T_finset_sum_loc]
  have hsumX := congrFun hsum X
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hTs] at hsumX ⊢; rw [hsumX, sub_self]
private theorem pureSpan : PureSpan_k := fun hT hF hPK F E _ _ _ _ _ σ d R Φ hΦ hTΦ => by
  obtain ⟨k, c, Φs, hi, heq⟩ := span_lift R (hT.1 F E σ d) (hF F E σ d R).1 R.fock (fun _ => True)
    (Submodule.span_le.2 fun _ ⟨P, g, hg, e⟩ => Submodule.subset_span ⟨P, g, trivial, hg, e⟩)
    (fun P φ _ hφ => Submodule.subset_span ⟨P, Dense.pf φ, Dense.pf_mem hφ, rfl⟩) hΦ.1 hTΦ
  refine ⟨k, c, Φs, fun i => ?_, heq⟩; obtain ⟨hsch, P, φ, -, hφ, hTi⟩ := hi i
  exact ⟨hPK F E σ d R (Φs i) hsch (hTi ▸ Submodule.subset_span ⟨P, Dense.pf φ, Dense.pf_mem hφ, rfl⟩),
    P, φ, fun v => hφ.1 v, hφ.2.mono fun _ hv => hv, by rw [hTi]; rfl⟩
private theorem vacSpan : VacSpan_k := fun hT hF hPK hVK F E _ _ _ _ _ σ d R Φ hΦ hTΦ => by
  have hvf : R.vac ≤ R.fock := (hVK F E σ d R).2.1
  obtain ⟨k, c, Φs, hi, heq⟩ := span_lift R (hT.1 F E σ d) (hF F E σ d R).1 R.vac (· = fun _ => 1)
    (Submodule.span_le.2 fun _ ⟨g, hg, e⟩ => Submodule.subset_span ⟨fun _ => 1, g, rfl, hg, e⟩)
    (fun P φ hp hφ => hvf (hp ▸ Submodule.subset_span ⟨Dense.pf φ, Dense.pf_mem hφ, rfl⟩)) hΦ hTΦ
  refine ⟨k, c, Φs, fun i => ?_, heq⟩; obtain ⟨hsch, P, φ, rfl, hφ, hTi⟩ := hi i
  have hmem : d.T (Φs i) ∈ R.vac := hTi ▸ Submodule.subset_span ⟨Dense.pf φ, Dense.pf_mem hφ, rfl⟩
  exact ⟨hPK F E σ d R (Φs i) hsch (hvf hmem), hmem, φ, fun v => hφ.1 v, hφ.2.mono fun _ hv => hv, by rw [hTi]; rfl⟩
private theorem genDictX : GenDictX_k :=
  fun hT hA F E _ _ _ _ _ σ d R Φ hΦ P gf hpg x ⟨t, u, hxtu⟩ nb lam 𝓖 hcd ε w hw T hTnd =>
    let ⟨η, hOf, hη, hherm, hof, hani, hcm, hJ, hTT⟩ := relAlg_pf_k F E σ d
    let ⟨T₀, hrat, hTdh, hTdd⟩ := hTT T hTnd
    let ⟨θ, fr, g, l, εs, Φg, Φf, Φv, hth, hfr, hg, hΦg, hεs, hchr, hpl, hfrm, hpf, hpr⟩ :=
      ThetaDictR.relReal_k F E σ d R Φ P gf hpg x t u hxtu η hη hherm
    let ⟨⟨μ, hsdW⟩, ⟨ν, hsdH⟩⟩ := sdEx F E σ hcm d.m (Jd_k d η) hJ d.B.ψ hchr d.n
    let hr : Rel_k d R x t u T η T₀ hOf θ fr g := ⟨hxtu, hrat, hη, hherm, hof, hth, hfr, hg⟩
    let ⟨lv, L₁, L₂, C, hC, hlv, hco, hstd, hht⟩ := heightDict F E σ d R x t u T η T₀ hOf θ fr g hr nb lam 𝓖 hcd ε w hw
    let ⟨hMβ, hMZ⟩ := measDict F E σ d R x t u T η T₀ hOf θ fr g hr
    let ⟨hembβ, hpresβ⟩ := hMβ nb lam 𝓖 hcd ν hsdH
    let ⟨νc, hνc⟩ := (hA F E σ d).1
    let ⟨hembZ, hpresZ⟩ := hMZ μ νc hsdW hνc
    let ⟨μH, 𝓕, hμH, h𝓕, horb⟩ := thetaDict_k F E σ d η hr.ne hr.herm
    by
      set c : ℂ := (d.χ t.det : ℂ) * (((absE F E t.det : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ)
      have hc0 : c ≠ 0 := mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2
        (Real.rpow_pos_of_pos (Ht.absE_pos t.det) _).ne')
      have hTx (Y) : d.T (d.om x Φ) (toMx Y) = c * Φg Y := by
        rw [hΦg Y]; exact (hT.2.1 F E σ d Φ hΦ.1).2.1 x t u hxtu (toMx Y)
      have hint (z : ℂ) (β : d.nA_) :
          GlobalTheory.ThK.Dbl.flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) =
          c * (C : ℂ) ^ (z - s0 d.m d.n) * Gen.whI (AF F) σ (Jd_k d η) d.B.ψ μ Φg (Gen.nuA θ g lv L₁ L₂)
            ((Td η T₀).map (SiegelWeilU.inclR (AF F))) z (hOf β) := by
        obtain ⟨hνpos, ha⟩ := hht β
        have hZ : ∫ Z, d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * d.gram Z Z))) * d.T (d.om x Φ) Z ∂νc =
            c * jtR (AF F) σ (Jd_k d η) d.B.ψ μ Φg (hOf β) := by
          rw [← hpresZ.integral_comp hembZ]; simp only [jtR, hTx, asm_phase_cell hr β]
          rw [← integral_const_mul]; congr 1; funext Y; ring
        simp only [GlobalTheory.ThK.Dbl.flat]
        rw [cellFormula hT F E σ d νc hνc ε w hw Φ hΦ.1 (nb β) x β.1 (hcd.1 β), hZ, ha, asm_phase_whit hr β,
          asm_cpow_split hC hνpos]; simp only [Gen.whI, s0]; ring
      refine ⟨2, Jd_k d η, Td η T₀, d.bs, d.B.ψ, θ, l, εs, fr, g, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c, C,
        ⟨hcm, hJ, hTdh, hTdd, hchr, hpl, hfrm, hlv, hco, hstd, hpf, hpr, hsdW, hsdH⟩, hani, hεs, hC,
        ⟨0, fun z _ => ⟨fun hI => ?_, ?_⟩⟩, μH, 𝓕, hμH, h𝓕, ?_⟩
      · have hk : c * (C : ℂ) ^ (z - s0 d.m d.n) ≠ 0 :=
          mul_ne_zero hc0 (Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hC.ne')))
        have h1 := hI.mul_bdd (lin_psi_meas_k d T.1.1).aestronglyMeasurable
          (Eventually.of_forall fun _ => (GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std _).le)
        refine (hpresβ.integrable_comp_emb hembβ).1 ((h1.const_mul (c * (C : ℂ) ^ (z - s0 d.m d.n))⁻¹).congr
          (Eventually.of_forall fun β => by simp only [hint z β]; exact inv_mul_cancel_left₀ hk _))
      · simp_rw [hint z]; rw [integral_const_mul, hpresβ.integral_comp hembβ]
      · rw [horb T T₀ hr.rat (d.om x Φ) (d.om_sch x Φ hΦ.1),
          show (fun Y => d.T (d.om x Φ) (toMx Y)) = fun Y => c * Φg Y from funext hTx, asm_meanC_smul]
private theorem linRedC : LinRedC_k := by
  intro hT hTC hLB hU hS c F E _ _ _ _ _ σ d hE k cs Φs hK x hW nb lam 𝓖 hcd ε w hw T hND
  have hTT := hT.2.2.2.1; have hTA := hT.2.2.2.2
  have hsum : ∑ i, cs i • Φs i ∈ d.sch := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hK i).1
  have hIfun : d.I (∑ i, cs i • Φs i) = ∑ i, cs i • d.I (Φs i) := by
    rw [Atop.I_sum d hTT hTA Finset.univ _ fun i _ => Submodule.smul_mem _ _ (hK i).1]
    exact Finset.sum_congr rfl fun i _ => Atop.I_smul d hTT (cs i) (hK i).1
  have hfc (s : Finset (Fin k)) : fc d.B.ψ d.b nb lam 𝓖 (∑ i ∈ s, cs i • d.I (Φs i)) T x =
      ∑ i ∈ s, cs i * fc d.B.ψ d.b nb lam 𝓖 (d.I (Φs i)) T x := by
    obtain ⟨hlin, -⟩ := hLB F E σ d (fun f => fc d.B.ψ d.b nb lam 𝓖 f T x) ⟨nb, lam, 𝓖, T, x, hcd, hND, rfl⟩
    have hc (s : Finset (Fin k)) : Continuous (∑ i ∈ s, cs i • d.I (Φs i)) := by
      rw [show (∑ i ∈ s, cs i • d.I (Φs i)) = fun a => ∑ i ∈ s, cs i * d.I (Φs i) a from
        funext fun _ => by simp [Finset.sum_apply]]
      exact continuous_finsetSum s fun i _ => continuous_const.mul ((hTA F E σ d).2.2 _ (hK i).1).2.1
    have hi (s : Finset (Fin k)) (γ) (hγ : γ ∈ d.r2) (g) :
        (∑ i ∈ s, cs i • d.I (Φs i)) (γ * g) = (∑ i ∈ s, cs i • d.I (Φs i)) g := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [((hTA F E σ d).2.2 _ (hK i).1).2.2 γ hγ g]
    induction s using Finset.induction_on with
    | empty =>
      have h0 := hlin 1 0 0 continuous_const continuous_const (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      simp only [one_smul, add_zero, one_mul] at h0; simpa using h0
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        hlin (cs j) (d.I (Φs j)) _ ((hTA F E σ d).2.2 _ (hK j).1).2.1 (hc s)
          ((hTA F E σ d).2.2 _ (hK j).1).2.2 (hi s), ih]
  have horbc : c * d.orb T (d.om x (∑ i, cs i • Φs i)) = ∑ i, cs i * (c * d.orb T (d.om x (Φs i))) := by
    rw [← hTC F E σ d _ hsum nb lam 𝓖 hcd T x, hIfun, hfc Finset.univ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hTC F E σ d _ (hK i).1 nb lam 𝓖 hcd T x]; ring
  choose t ht using fun i => hU F E σ d d.s₀ (d.sec0 (Φs i)) (hS F E σ d (Φs i) (hK i)) (hE (Φs i) (hK i))
  have hval := lin_holValueAt_sum Finset.univ cs
    (fun i z => ∫ β, GlobalTheory.ThK.Dbl.flat d.a (d.sec0 (Φs i)) d.s₀ z (w * nb β * x) *
      d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
    (fun i => c * d.orb T (d.om x (Φs i))) d.s₀ (fun i _ => hW i nb lam 𝓖 hcd ε w hw T hND)
  rw [horbc]; refine hval.congr ⟨∑ i, |t i|, fun z hz => ?_⟩
  have hint (i) : Integrable (fun β => GlobalTheory.ThK.Dbl.flat d.a (d.sec0 (Φs i)) d.s₀ z (w * nb β * x) *
      d.B.ψ (-d.tt (T.1.1 * β.1))) lam :=
    ((ht i z (lt_of_le_of_lt ((le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (t j))
      (Finset.mem_univ i))) hz) nb lam 𝓖 hcd ε w hw x).1).mul_bdd (lin_psi_meas_k d T.1.1).aestronglyMeasurable
      (Eventually.of_forall fun _ => (GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std _).le)
  refine (Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm).trans <|
    (integral_finsetSum Finset.univ fun i _ => (hint i).const_mul (cs i)).symm.trans ?_
  congr 1; funext β
  simp only [GlobalTheory.ThK.Dbl.flat, SD_k.sec0, map_sum, map_smul, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring
end W
end KWhit

section
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
open TBij.Adp KTunit GlobalTheory.TowU
private def rp_loc (d : SD_k σ) (Y W : d.ME) : F := Algebra.trace F E (Yᵀ * d.A.J * W.map σ).trace
private def eqm_loc (d : SD_k σ) (q : d.I3) : d.ME :=
  Matrix.of fun i j => if (i, j) = (q.1, q.2.1) then d.bs q.2.2 else 0
private def rc_loc (d : SD_k σ) : d.ME ≃ₗ[F] (d.I3 → F) :=
  { toFun := fun Y k => d.bs.repr (Y k.1 k.2.1) k.2.2
    invFun := fun a => Matrix.of fun i j => ∑ k, a (i, j, k) • d.bs k
    left_inv := fun Y => by ext i j; exact d.bs.sum_repr (Y i j)
    right_inv := fun a => funext fun ⟨i, j, k⟩ => congrFun (d.bs.repr_sum_self fun k' => a (i, j, k')) k
    map_add' := fun _ _ => funext fun _ => by simp, map_smul' := fun _ _ => funext fun _ => by simp }
private def Lm_loc (d : SD_k σ) (ε : ℤˣ) : (d.I3 → F) →ₗ[F] (d.I3 → F) where
  toFun a q := ((ε : ℤ) : F) * rp_loc d ((rc_loc d).symm a) (eqm_loc d q)
  map_add' a b := funext fun q => by
    simp only [map_add (f := _), rp_loc, Matrix.transpose_add, Matrix.add_mul, Matrix.trace_add, Pi.add_apply]; ring
  map_smul' c a := funext fun q => by
    simp only [map_smul, rp_loc, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring
private theorem Lm_inj_loc (d : SD_k σ) (ε : ℤˣ) : Function.Injective (Lm_loc d ε) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']; intro a ha
  have hε : ((ε : ℤ) : F) ≠ 0 := by rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  set Y := (rc_loc d).symm a
  have hq (q) : rp_loc d Y (eqm_loc d q) = 0 := (mul_eq_zero.1 (by simpa [Lm_loc] using congrFun ha q)).resolve_left hε
  have h0 : Yᵀ * d.A.J = 0 := Matrix.ext fun j i => (traceForm_nondegenerate F E).1 _ fun z => by
    obtain ⟨e, rfl⟩ := (AlgHom.bijective σ).2 z
    rw [Algebra.traceForm_apply, ← d.bs.sum_repr e, map_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    have htr : rp_loc d Y (eqm_loc d (i, j, k)) = Algebra.trace F E ((Yᵀ * d.A.J) j i * σ (d.bs k)) := by
      unfold rp_loc; congr 1
      rw [Matrix.trace, Finset.sum_eq_single j (fun b _ hb => by
        rw [Matrix.diag_apply, Matrix.mul_apply]; exact Finset.sum_eq_zero fun _ _ => by simp [eqm_loc, hb]) (by simp),
        Matrix.diag_apply, Matrix.mul_apply, Finset.sum_eq_single i (fun b _ hb => by simp [eqm_loc, hb]) (by simp)]
      simp [eqm_loc]
    rw [AlgHom.map_smul_of_tower, mul_smul_comm, map_smul, ← htr, hq, smul_zero]
  have h1 : Yᵀ = 0 := by
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (KWhit.meas_detA_k d))] using
      congrArg (· * d.A.J⁻¹) h0
  simpa [Y] using congrArg (rc_loc d) (show Y = 0 by rw [← Matrix.transpose_transpose Y, h1, Matrix.transpose_zero])
private theorem poisson_loc : TW.Poisson_k := by
  intro F E _ _ _ _ _ σ d ν hν ε f hf
  have hrat (X : d.MxE) : X ∈ d.ratM ↔ d.crd X ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice F d.I3 := by
    let c : d.MxE →+ (d.I3 → AF F) := ⟨⟨d.crd, funext fun _ => by simp [SD_k.crd]⟩,
      fun _ _ => funext fun _ => KFock.crd_add_k d _ _ _⟩
    refine ⟨fun hX => ((AddSubgroup.closure_le
        ((GroundTheory.Automorphic.FourierWhittaker.vecLattice F d.I3).comap c)).mpr <| by
      rintro _ ⟨M, rfl⟩
      exact ⟨fun k => d.bs.repr (M k.1 k.2.1) k.2.2, funext fun k => (TBij_k.Adp.crd_incM d M k).symm⟩) hX, ?_⟩
    rintro ⟨ξ, hξ⟩; let M : d.ME := Matrix.of fun i j => ∑ k, ξ (i, j, k) • d.bs k
    have e1 : d.crd (incM F M) = d.crd X := funext fun k => by
      rw [TBij_k.Adp.crd_incM d _ k]; have h2 := congrFun hξ k
      simp only [AddMonoidHom.compLeft, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply] at h2
      rw [← h2]; show _ = algebraMap F (AF F) (ξ k)
      congr 1; exact congrFun (d.bs.repr_sum_self fun k' => ξ (k.1, k.2.1, k')) k.2.2
    rw [show X = incM F M by rw [← KFock.cmb_crd_k d (incM F M), e1, KFock.cmb_crd_k]]
    exact AddSubgroup.subset_closure ⟨_, rfl⟩
  have hcov (h : d.MF) :
      ∫ Z, h Z ∂ν = ∫ c, h (d.cmb c) ∂(GroundTheory.Automorphic.GJMatrix.adeleMeasurePi F (ι := d.I3)) := by
    obtain ⟨_, _, _, hB, _⟩ := KWhit.meas_mx_top'_loc d; obtain ⟨hH, 𝓕, h𝓕, h1⟩ := hν
    exact TW.Twp.integral_cov_gen (hBor := hB) (hνH := hH) d.ratM (cEquiv_k d (Equiv.refl _)) hrat ν 𝓕 h𝓕 h1 h
  have hpair (Y : d.ME) (Z : d.MxE) : ((ε : ℤ) : AF F) * d.tt (d.gram (incM F Y) Z) =
      ∑ q, d.crd Z q * algebraMap F (AF F) (Lm_loc d ε (rc_loc d Y) q) := by
    have hek (q : d.I3) : TBij_k.Adp.ek d q = incM F (eqm_loc d q) := by
      rcases q with ⟨i0, j0, k0⟩; ext i j
      simp only [TBij_k.Adp.ek, SD_k.cmb, incM, Matrix.map_apply, eqm_loc, Matrix.of_apply]
      show _ = (1 : AF F) ⊗ₜ[F] _; by_cases h : (i, j) = (i0, j0)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rw [ite_eq_left rfl, Finset.sum_eq_single k0 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]; simp
      · rw [ite_eq_right h, TensorProduct.tmul_zero]
        exact Finset.sum_eq_zero fun k _ => by
          simp [show (i0, j0, k0) ≠ (i, j, k) from fun e =>
            h (by simp only [Prod.mk.injEq] at e; exact Prod.ext e.1.symm e.2.1.symm)]
    let ttL : d.MxE →ₗ[AF F] AF F :=
      ⟨⟨fun W => d.tt (d.gram (incM F Y) W), fun W W' => by
          have e : (W + W').map (cA σ) = W.map (cA σ) + W'.map (cA σ) := Matrix.map_add _ (map_add _) _ _
          simp only [SD_k.tt, SD_k.gram, e, Matrix.mul_add, Matrix.trace_add, map_add (f := _)]⟩,
       fun a W => by
          have e : (a • W).map (cA σ) = a • W.map (cA σ) := Matrix.map_smul _ a (fun x => map_smul (cA σ) a x) _
          simp only [SD_k.tt, SD_k.gram, e, Matrix.mul_smul, Matrix.trace_smul, map_smul, RingHom.id_apply]⟩
    have hs : d.tt (d.gram (incM F Y) Z) = ∑ q, d.crd Z q * d.tt (d.gram (incM F Y) (incM F (eqm_loc d q))) := by
      change ttL Z = _
      conv_lhs => rw [← KFock.cmb_crd_k d Z, TBij_k.Adp.cmb_sum]
      simp only [hek, map_sum, map_smul, smul_eq_mul]; rfl
    rw [hs, Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => ?_
    have hgi : d.tt (d.gram (incM F Y) (incM F (eqm_loc d q))) = algebraMap F (AF F) (rp_loc d Y (eqm_loc d q)) := by
      rw [SD_k.gram, TBij.cA_incM, ← TBij.incM_transpose, ← TBij.incM_mul, ← TBij.incM_mul, SD_k.tt, rp_loc]
      rw [show (incM F (Yᵀ * d.A.J * (eqm_loc d q).map σ)).trace =
          (1 : AF F) ⊗ₜ[F] (Yᵀ * d.A.J * (eqm_loc d q).map σ).trace by
        simp only [Matrix.trace, incM, Matrix.diag_apply, Matrix.map_apply, TensorProduct.tmul_sum]; rfl,
        TW.Twp.trace_tmul', one_mul]
    rw [hgi]
    simp only [Lm_loc, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply, map_mul, map_intCast]; ring
  have hfour (Y : d.ME) : ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (incM F Y) Z)) * f Z ∂ν =
      GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c))
        (fun q => algebraMap F (AF F) (Lm_loc d ε (rc_loc d Y) q)) := by
    rw [hcov, GroundTheory.Automorphic.GJMatrix.adelicFourierPi]; congr 1; funext c
    rw [hpair Y (d.cmb c), KFock.crd_cmb_k, GlobalTheory.AdelicSvN.Weyl.isStd_eq d.ok.good.std, mul_comm]
  refine (tsum_congr hfour).trans <| ((rc_loc d).toEquiv.tsum_eq _).trans <|
    ((LinearEquiv.ofInjectiveEndo (Lm_loc d ε) (Lm_inj_loc d ε)).toEquiv.tsum_eq _).trans <|
    (FourWeyl.theta_four (Submodule.mem_comap.1 hf : (fun c => f (d.cmb c)) ∈ schA F d.I3)).trans ?_
  show ∑' ξ : d.I3 → F, f (d.cmb fun q => algebraMap F (AF F) (ξ q)) = _
  have e (X : d.ME) : f (incM F X) = f (d.cmb fun q => algebraMap F (AF F) (rc_loc d X q)) :=
    congrArg f ((KFock.cmb_crd_k d (incM F X)).symm.trans (congrArg d.cmb (funext fun q => TBij_k.Adp.crd_incM d X q)))
  simp_rw [e]; exact ((rc_loc d).toEquiv.tsum_eq fun a => f (d.cmb fun q => algebraMap F (AF F) (a q))).symm
private theorem uniq_loc : TW.Uniq_k := by
  intro F E _ _ _ _ _ σ d ν hν Λ hΛ hinv; have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨τ, S0, S0', C, hop, hT⟩ := Tunit.T_chart_k d
  by_cases hC : C = 0
  · refine ⟨0, fun Φ hΦ => ?_⟩
    rw [(TBij_k.tBij F E σ d).2.2 Φ hΦ (funext fun X => by rw [hT Φ hΦ X, hC, zero_mul]; rfl), map_zero, zero_mul]
  have rhoS' (w φ) (hφ : φ ∈ schA F d.κ) : S0' (schr d.B.ψ (TBij_k.Adp.c0 d τ w) φ) = d.dd.rho d.B.ψ w (S0' φ) := by
    have h1 : S0 (d.dd.rho d.B.ψ w (S0' φ)) = schr d.B.ψ (TBij_k.Adp.c0 d τ w) φ := by
      simp only [Darboux.rho]; rw [hop.Heisenberg₂ _ _ (hop.pres' φ hφ), LinearEquiv.symm_apply_apply, hop.right φ hφ]
    rw [← h1, hop.left _ (show d.dd.rho d.B.ψ w (S0' φ) ∈ d.sch from
      GlobalTheory.HeisSchA.schr_mem_schA d.B.ψ hψ _ _ (hop.pres' φ hφ))]
  let : MeasurableSpace (d.κ → AF F) := borel _; obtain ⟨hμ, hint⟩ := map_haar_k d τ ν hν
  obtain ⟨c, hc⟩ := TW.Twu.translation_invariant_functional_haar d.B.ψ hψ d.κ (ν.map (cmap_k d τ)) hμ (Λ ∘ₗ S0')
      (hop.adm' Λ hΛ) (fun a φ hφ => by
    have e0 := TBij_k.Adp.coordinates_frame d τ (cinv_k d τ a)
    rw [show (fun k => d.crd (cinv_k d τ a) (τ k)) = a from cmap_cinv_k d τ a] at e0
    rw [← TW.Twu.schr_zero_right, ← e0, LinearMap.comp_apply, LinearMap.comp_apply, rhoS' _ φ hφ]
    exact hinv _ _ (hop.pres' φ hφ))
  refine ⟨c / C, fun Φ hΦ => ?_⟩
  have h1 := hc (S0 Φ) (hop.pres Φ hΦ); rw [LinearMap.comp_apply, hop.left Φ hΦ] at h1
  have e2 : ∫ Z, d.T Φ Z ∂ν = C * ∫ Z, S0 Φ (cmap_k d τ Z) ∂ν := by
    rw [← integral_const_mul]; exact integral_congr_ae (Filter.Eventually.of_forall fun Z => hT Φ hΦ Z)
  rw [h1, ← hint, e2]; field_simp
end
private theorem iwaQ_loc (hT : TAll_k) : IwaQ_k := by
  intro F E _ _ _ _ _ σ d L x; obtain ⟨p, k, lam, hk, rfl, hp⟩ := Avac.line_fix'_k L.i₀ x
  obtain ⟨ε, hd, hL⟩ := Avac.eps_eq_k L; obtain ⟨g, hq⟩ := Avac.q_split'_k L ε hd hL p lam hp
  set q := p * (L.j g)⁻¹ with hqdef; obtain ⟨c, hc⟩ := Avac.q_T'_k hT L.i₀ hq
  refine ⟨q, g, k, (absE F E lam : ℝ), c, hk, by simp [hqdef, mul_assoc], _root_.PositivityTheory.SiegelWeilFormula.KSplitP.absE_pos lam, fun g' => ?_,
      fun Φ hΦ g' X hX => ?_⟩
  · have e : L.j g' * (p * k) = (L.j g' * q * (L.j g')⁻¹) * L.j (g' * g) * k := by
      simp only [hqdef, map_mul, mul_assoc, inv_mul_cancel_left]
    rw [e, KWhit.a_mul_K_k d _ k hk, Avac.q_ht'_k L (Avac.q_conj'_k L hq g') (g' * g)]
  · set Ψ := d.om q Φ - c • Φ with hΨ
    have hΨs : Ψ ∈ d.sch := sub_mem (d.om_sch q Φ hΦ) (Submodule.smul_mem _ c hΦ)
    have hTΨ (X : d.MxE) (hX : ∀ a, X a L.i₀ = 0) : d.T Ψ X = 0 := by
      rw [hΨ, congrFun (KFock.T_sub_k d _ _) X, Pi.sub_apply, congrFun (KFock.T_smul_k d c Φ) X,
        Pi.smul_apply, smul_eq_mul, hc Φ hΦ X hX, sub_self]
    have key := L.res Ψ hΨs 0 (zero_mem _) (fun X hX => by rw [L.sd.T_zero, hTΨ X hX]; rfl) g' X hX
    rw [map_zero, L.sd.T_zero] at key; have h0 := key.symm
    rw [map_mul, mul_apply_eq_comp]
    rw [show d.om (L.j g') Ψ = d.om (L.j g') (d.om q Φ) - c • d.om (L.j g') Φ by rw [hΨ, map_sub, map_smul],
      congrFun (KFock.T_sub_k d _ _) X, Pi.sub_apply,
      congrFun (KFock.T_smul_k d c _) X, Pi.smul_apply, smul_eq_mul] at h0
    exact sub_eq_zero.1 h0

private def vg_loc {d : SD_k σ} (R : RD_k d) (g : d.Af3 → ℂ) (X : d.MxE) : ℂ :=
  (∏ w, fP 1 (R.loc w X)) * g fun k => (d.crd X k).2
private theorem vacK_loc (hT : TAll_k) (hF : FockMem_k) (hO : LocOpEx_k) (hI : LocInst_k) (hA : FinAct_k) : VacK_k := by
  intro F E _ _ _ _ _ σ d R
  have hleF {d' : SD_k σ} (R'' : RD_k d') : R''.vac ≤ R''.fock :=
    Submodule.span_le.2 fun _ ⟨g, hg, h⟩ => h ▸ Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
  have hlocAdd (w : InfinitePlace F) {Z : d.MxE} (hZ : d.cw w Z = 0) (X) : R.loc w (X + Z) = R.loc w X := by
    unfold RD_k.loc; rw [show d.cw w (X + Z) = d.cw w X by
      simp only [SD_k.cw] at hZ ⊢; rw [Matrix.map_add _ (map_add _), hZ, add_zero]]
  refine ⟨?_, hleF R, fun L R' Φ hΦ hv => ?_⟩
  · let S' : Submodule ℂ d.Fn :=
      { carrier := {Φ | Φ ∈ d.sch ∧ ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac}
        zero_mem' := ⟨zero_mem _, fun _ _ => by rw [map_zero, d.T_zero]; exact zero_mem _⟩
        add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, fun k hk => by
          rw [map_add (f := _), KFock.T_add_k]; exact add_mem (ha.2 k hk) (hb.2 k hk)⟩
        smul_mem' := fun c _ ha => ⟨Submodule.smul_mem _ c ha.1, fun k hk => by
          rw [map_smul, KFock.T_smul_k]; exact Submodule.smul_mem _ c (ha.2 k hk)⟩ }
    have hpeel : ∀ (S : Finset (InfinitePlace F)) (k : d.G),
        (∀ w ∈ S, d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1) →
        (∀ w ∉ S, d.cw w (inFrame d.b k) = 1) → ∀ g ∈ SB d.Af3, ∀ Φ ∈ d.sch,
          d.T Φ = vg_loc R g → ∃ g' ∈ SB d.Af3, d.T (d.om k Φ) = vg_loc R g' := fun S => by
      induction S using Finset.induction_on with
      | empty =>
        intro k _ h1 g hg Φ hΦ hTΦ
        obtain ⟨g', hg', H⟩ := hA F E σ d k (fun w => h1 w (Finset.notMem_empty w)) g hg
        exact ⟨g', hg', H _ (fun X Z h => Finset.prod_congr rfl fun w _ => by rw [hlocAdd w (h w)]) Φ hΦ hTΦ⟩
      | insert w S hw ih =>
        intro k h0 h1 g hg Φ hΦ hTΦ
        have hζ0 := Krd.zeta_ne R.hζ; set M := d.cw w (inFrame d.b k) with hM
        have hY := Krd.inG_conj R.hζ M (hM ▸ KSing.UnitaryGroupBasics.form_w_k d R w k)
        have hMM : Mᴴ * M = 1 :=
          (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 (hM ▸ h0 w (Finset.mem_insert_self w S))
        set y : GR d.n := KSing.UnitaryGroupBasics.mkGR _ hY
        have hy : InK (mR y) := ⟨hY, by
          show (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹)ᴴ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹) = 1
          have hsz : star R.ζ = R.ζ⁻¹ := by rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
          have hdZ (a b : ℂ) (hab : star a = b) : (dZ d.n a)ᴴ = dZ d.n b := by
            simp [dZ, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul, hab]
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hdZ _ _ hsz, hdZ _ _ (by rw [← hsz, star_star])]
          calc dZ d.n R.ζ * (Mᴴ * dZ d.n R.ζ⁻¹) * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹)
              = dZ d.n R.ζ * (Mᴴ * (dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) * M) * dZ d.n R.ζ⁻¹ := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, hMM, Matrix.mul_one, Krd.dZ_mul_inv hζ0]⟩
        have hyw : d.cw w (inFrame d.b (R.ι w y)) = M := by
          have h := congrArg (dZ d.n R.ζ⁻¹ * ·) (R.at_w w y)
          simp only [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul] at h
          rw [h]; show dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹) * dZ d.n R.ζ = M
          simp only [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
          rw [Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.mul_one]
        have hcwI (w') : d.cw w' (inFrame d.b ((R.ι w y)⁻¹ * k)) =
            d.cw w' (inFrame d.b (R.ι w y)⁻¹) * d.cw w' (inFrame d.b k) := by rw [d.inFrame_mul, Krd.cw_mul_k]
        have hkw : d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by
          rw [hcwI, ← hM, ← hyw, ← Krd.cw_mul_k, ← d.inFrame_mul, inv_mul_cancel, d.inFrame_one, Krd.cw_one_k]
        have hkw' (w') (he : w' ≠ w) : d.cw w' (inFrame d.b ((R.ι w y)⁻¹ * k)) = d.cw w' (inFrame d.b k) := by
          rw [hcwI, show d.cw w' (inFrame d.b (R.ι w y)⁻¹) = 1 from by rw [← map_inv]; exact R.off_w w w' y⁻¹ he,
            Matrix.one_mul]
        obtain ⟨g₁, hg₁, e₁⟩ := ih ((R.ι w y)⁻¹ * k)
          (fun w' h => by rw [hkw' w' (fun e => hw (e ▸ h))]; exact h0 w' (Finset.mem_insert_of_mem h))
          (fun w' h => by by_cases e : w' = w; · rw [e, hkw]
                          · rw [hkw' w' e]; exact h1 w' fun h' => (Finset.mem_insert.1 h').elim e h) g hg Φ hΦ hTΦ
        obtain ⟨Lop, hLop⟩ := hO F E σ d R w; obtain ⟨sL, ρ, p, q, e, -, hld, -, hkL⟩ := hI F E σ d R w Lop hLop
        let psiW (g' : d.Af3 → ℂ) (X : d.MxE) : ℂ :=
          (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X)) * g' fun k => (d.crd X k).2
        have hvt (g' : d.Af3 → ℂ) : vg_loc R g' = R.tens w (fP 1) (psiW g') := funext fun X => by
          simp only [vg_loc, RD_k.tens, psiW]; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]; ring
        have hpi : d.Indep w (psiW g₁) := fun X Z hZ1 hZ2 => by
          have e2 : (fun k => (d.crd (X + Z) k).2) = fun k => (d.crd X k).2 := funext fun k => by
            rw [KFock.crd_add_k]; change (d.crd X k).2 + (d.crd Z k).2 = _; rw [KFock.crd_fin_k d Z hZ2 k, add_zero]
          dsimp only [psiW]
          rw [Finset.prod_congr rfl fun w' hw' => by rw [hlocAdd w' (hZ1 w' (Finset.ne_of_mem_erase hw'))], e2]
        have hL1 := (hLop y _ (KFock.isSw_fP 1)).2 (psiW g₁) hpi _ (d.om_sch _ Φ hΦ) (e₁.trans (hvt g₁))
        refine ⟨F0 p q e y • g₁, Submodule.smul_mem _ _ hg₁, ?_⟩
        rw [show k = R.ι w y * ((R.ι w y)⁻¹ * k) from (mul_inv_cancel_left _ _).symm, map_mul, mul_apply_eq_comp,
          hL1, hkL y 1 hy, hld.kvac y hy, hvt]
        funext X; simp only [RD_k.tens, psiW, Pi.smul_apply, smul_eq_mul, fP, evX, MvPolynomial.smul_eq_C_mul, mul_one,
          MvPolynomial.eval_C, map_one, one_mul]; ring
    have hle : R.vac ≤ S'.map (KK.W.Tl d) := Submodule.span_le.2 fun _ ⟨g, hg, hEq⟩ => by
      subst hEq
      obtain ⟨Φ, hΦ, e⟩ := (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 (hleF R (Submodule.subset_span ⟨g, hg, rfl⟩)))
      refine ⟨Φ, ⟨hΦ, fun k hk => ?_⟩, e⟩
      obtain ⟨g', hg', e'⟩ := hpeel Finset.univ k (fun w _ => ((d.ok.stdK k).1 hk).1 w)
        (fun w h => absurd (Finset.mem_univ w) h) g hg Φ hΦ e
      rw [e']; exact Submodule.subset_span ⟨g', hg', rfl⟩
    intro Φ hΦ hv k hk; obtain ⟨Φ', hΦ', e⟩ := hle hv; rw [← KFock.T_inj_k hT.1 d hΦ'.1 hΦ e]; exact hΦ'.2 k hk
  · let ins (z : Fin d.m × Fin L.n × Fin 2 → Af F) : d.I3 → Af F :=
      fun k => if h : ∃ j, L.em j = k.2.1 then z (k.1, h.choose, k.2.2) else 0
    let extM (X' : Mx F E d.m L.n) : d.MxE := fun a i => if h : ∃ j, L.em j = i then X' a h.choose else 0
    let resL : d.MF →ₗ[ℂ] (Mx F E d.m L.n → ℂ) := LinearMap.funLeft ℂ ℂ extM
    have hci : Continuous ins := continuous_pi fun k => by
      by_cases h : ∃ j, L.em j = k.2.1 <;> simp only [ins, h, ↓reduceDIte]
      · exact continuous_apply _
      · exact continuous_const
    have hle1 : R.vac ≤ R'.vac.comap resL := Submodule.span_le.2 fun _ ⟨g, hg, hEq⟩ => by
      subst hEq
      have hge (w X') : fP 1 (R.loc w (extM X')) = fP 1 (R'.loc w X') := by
        suffices key : ∑ a, ∑ i, ‖R'.loc w X' a i‖ ^ 2 = ∑ a, ∑ i, ‖R.loc w (extM X') a i‖ ^ 2 by
          simp only [fP, gs, key, evX, map_one]
        have hsl {d' : SD_k σ} (R'' : RD_k d') (X : d'.MxE) :
            ∑ a, ∑ i, ‖R''.loc w X a i‖ ^ 2 = ∑ i, ∑ a, ‖(((R''.fr w)⁻¹).1 *ᵥ fun b => d'.cw w X b i) a‖ ^ 2 := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
            simp only [RD_k.loc, Matrix.map_apply, norm_star]; rfl
        rw [hsl R', hsl R]; refine Fintype.sum_of_injective L.em L.inj _ _ (fun i hi => ?_) (fun j => ?_)
        · have h : ¬ ∃ j, L.em j = i := fun ⟨j, hj⟩ => hi ⟨j, hj⟩
          have : (fun b => d.cw w (extM X') b i) = 0 := funext fun b => by
            change (piInf (d.B.emb w)) (extM X' b i) = 0; simp only [extM, dite_eq_right h, map_zero]
          simp [this]
        · have h : ∃ j', L.em j' = L.em j := ⟨_, rfl⟩
          have e : (fun b => d.cw w (extM X') b (L.em j)) = fun b => L.sd.cw w X' b j := funext fun b => by
            change (piInf (d.B.emb w)) (extM X' b (L.em j)) = (piInf (d.B.emb w)) (X' b j)
            simp only [extM, dite_eq_left h, L.inj h.choose_spec]
          rw [e]; exact Avac.norm_frame_eq d.ok.hm (d.A.J.map (d.B.emb w).1) (R'.fr w) (R.fr w) R'.ζ R.ζ (R'.sg w)
            (R.sg w) (R'.hζ.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
            (R.hζ.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)) (R'.hfr w) (R.hfr w) _
      have hrv : resL (vg_loc R g) = vg_loc R' (fun z => g (ins z)) := funext fun X' => by
        show vg_loc R g (extM X') = _; simp only [vg_loc]; congr 1
        · exact Finset.prod_congr rfl fun w _ => hge w X'
        · congr 1; funext k; by_cases h : ∃ j, L.em j = k.2.1
          · simp only [SD_k.crd, extM, ins, dite_eq_left h]
          · simp only [SD_k.crd, extM, ins, dite_eq_right h, map_zero, Finsupp.coe_zero, Pi.zero_apply]; rfl
      show resL (vg_loc R g) ∈ R'.vac; rw [hrv]
      refine Submodule.subset_span ⟨fun z => g (ins z), ⟨hg.1.comp_continuous hci, ?_⟩, rfl⟩
      let prj (z : d.I3 → Af F) : Fin d.m × Fin L.n × Fin 2 → Af F := fun k => z (k.1, L.em k.2.1, k.2.2)
      have hc : IsCompact (prj '' tsupport g) := hg.2.isCompact.image (continuous_pi fun _ => continuous_apply _)
      exact hc.of_isClosed_subset (isClosed_tsupport _) ((tsupport_comp_subset_preimage g hci).trans fun z hz =>
        ⟨ins z, hz, funext fun k => by
          have h : ∃ j, L.em j = L.em k.2.1 := ⟨_, rfl⟩
          simp only [prj, ins, dite_eq_left h, L.inj h.choose_spec]⟩)
    have h1 : resL (d.T Φ) ∈ R'.vac := hle1 hv
    obtain ⟨Φ', hΦ', e⟩ := (hT.1 F E σ L.sd).2.1 _ ((hF F E σ L.sd R').1 (hleF R' h1))
    refine ⟨Φ', ⟨hΦ', fun X hX => ?_⟩, e ▸ h1⟩
    rw [e]; show d.T Φ (extM (X.submatrix id L.em)) = d.T Φ X
    congr 1; funext a i; by_cases h : ∃ j, L.em j = i
    · simp only [extM, dite_eq_left h, Matrix.submatrix_apply, id, h.choose_spec]
    · simp only [extM, dite_eq_right h]; rw [by_contra fun hi => h ((L.rng i).1 hi), hX]
section PolyKFin
open KK KK.W
private theorem var_span' {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (k : Fin d.m × Fin d.n × Bool) :
    ∃ (Z₁ Z₂ : M1 d) (c₁ c₂ : ℂ), At (evI F) Z₁ ∧ At (evI F) Z₂ ∧
      ∀ X, evX (MvPolynomial.X k) (R.loc w X) = c₁ * (mZ d Z₁ X : ℂ) + c₂ * (mZ d Z₂ X : ℂ) := by
  obtain ⟨tA, htA⟩ := c1_eq_dg_mul (d := d)
  set fr := (R.fr w).1; set fi := ((R.fr w)⁻¹).1; set A := d.A.J.map (d.B.emb w).1; set e : ℂ := ((R.ε : ℤ) : ℂ)
  have he : e * e = 1 := by rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]
  have hz : star R.ζ * R.ζ = 1 := by rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
  have hfi : fr * fi = 1 := by simp only [fr, fi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hif : fi * fr = 1 := by simp only [fr, fi]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set P := (((R.sg w : ℤ) : ℂ) * R.ζ) • (fr.map star * frᵀ)
  have hAP : A * P = 1 := by
    rw [show A = d.A.J.map (d.B.emb w).1 from rfl, A_eq hfi hz (R.hfr w)]
    simp only [P, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have t1 : fiᵀ * fi.map star * (fr.map star * frᵀ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fi.map star), ← mapStar_mul, hif,
        show (1 : Matrix (Fin d.m) (Fin d.m) ℂ).map star = 1 from Matrix.map_one star (star_zero _) (star_one _),
        Matrix.one_mul, ← Matrix.transpose_mul, hfi, Matrix.transpose_one]
    have hs2 : ((R.sg w : ℤ) : ℂ) * R.ζ * (((R.sg w : ℤ) : ℂ) * star R.ζ) = 1 := by
      calc _ = (((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * (star R.ζ * R.ζ) := by ring
        _ = 1 := by rw [hz, mul_one]; rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h]
    rw [t1, hs2, one_smul]
  have mapI {p q : Type} (w' : InfinitePlace F) (M : Matrix p q E) :
      (incM F M).map (piInf (d.B.emb w')) = M.map (d.B.emb w').1 := Krd.cw_incM_k d w' M
  have key (M : Matrix (Fin d.m) (Fin d.n) ℂ) : ∃ Z : M1 d, At (evI F) Z ∧
      ∀ X, (mZ d Z X : ℂ) = -(2 * e) * ((Matrix.trace ((d.cw w X)ᵀ * M)).re : ℂ) := by
    choose x hx hz' using fun i j => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ d.ok.good.cm
      d.B.emb fun w' => if w' = w then ((P * M).map star) i j else 0
    refine ⟨Matrix.of x * tAᵀ, at_mul' (fun c hc => Matrix.ext fun i j => hx i j c hc) _, fun X => ?_⟩
    have hV (w') : d.cw w' (Matrix.of x) = if w' = w then (P * M).map star else 0 := Matrix.ext fun i j => by
      show piInf (d.B.emb w') (x i j) = _; rw [hz' i j w']; split_ifs <;> rfl
    have e1 : Matrix.of x * tAᵀ * (dg d)ᵀ = Matrix.of x * (c1 d)ᵀ := by rw [htA, Matrix.transpose_mul, Matrix.mul_assoc]
    have hmZ : mZ d (Matrix.of x * tAᵀ) X =
        -(2 * (e * Matrix.trace ((d.cw w X)ᵀ * A * ((P * M).map star).map star)).re) := by
      rw [mZ, e1, trace_sp, Finset.sum_eq_single w (fun w' _ hw' => by
        rw [show (Matrix.of x * (c1 d)ᵀ).map (piInf (d.B.emb w')) = 0 from by
          rw [Matrix.map_mul, Matrix.transpose_map, mapI, show (Matrix.of x).map (piInf (d.B.emb w')) =
            d.cw w' (Matrix.of x) from rfl, hV w', ite_eq_right hw', Matrix.zero_mul]]; simp) (by simp)]
      congr 3
      rw [show (X * (c2 d)ᵀ).map (piInf (d.B.emb w)) = d.cw w X * ((d.b.1.map (d.B.emb w).1).toCols₂)ᵀ from by
          rw [Matrix.map_mul, Matrix.transpose_map, mapI]; rfl,
        show (Matrix.of x * (c1 d)ᵀ).map (piInf (d.B.emb w)) =
          (P * M).map star * ((d.b.1.map (d.B.emb w).1).toCols₁)ᵀ from by
          rw [Matrix.map_mul, Matrix.transpose_map, mapI, show (Matrix.of x).map (piInf (d.B.emb w)) =
            d.cw w (Matrix.of x) from rfl, hV w, ite_eq_left rfl]; rfl]
      exact trace_form_sign_eq (frame_form R w) (d.cw w X) ((P * M).map star)
    have hPM : (d.cw w X)ᵀ * A * ((P * M).map star).map star = (d.cw w X)ᵀ * M := by
      rw [show ((P * M).map star).map star = P * M from
          Matrix.ext fun _ _ => by simp only [Matrix.map_apply, star_star],
        ← Matrix.mul_assoc, Matrix.mul_assoc _ A, hAP, Matrix.mul_one]
    rw [hmZ, hPM]; rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]
  have hM (c : ℂ) (x : Matrix (Fin d.m) (Fin d.n) ℂ) :
      Matrix.trace (xᵀ * Matrix.of fun b j => if j = k.2.1 then c * fi k.1 b else 0) = c * (fi * x) k.1 k.2.1 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, mul_ite,
      mul_zero]
    rw [Finset.sum_eq_single k.2.1 (fun j _ hj => by simp [hj]) (by simp), Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by simp only [ite_true]; ring
  obtain ⟨Z₁, h1, e1⟩ := key (Matrix.of fun b j => if j = k.2.1 then 1 * fi k.1 b else 0)
  obtain ⟨Z₂, h2, e2⟩ := key (Matrix.of fun b j => if j = k.2.1 then (-Complex.I) * fi k.1 b else 0)
  have hl (X) : evX (MvPolynomial.X k) (R.loc w X) =
      if k.2.2 then (fi * d.cw w X) k.1 k.2.1 else star ((fi * d.cw w X) k.1 k.2.1) := by
    simp only [evX, MvPolynomial.eval_X, RD_k.loc, Matrix.map_apply]; split_ifs <;> (try simp only [star_star]) <;> rfl
  refine ⟨Z₁, Z₂, -(e / 2), -(e / 2) * (if k.2.2 then Complex.I else -Complex.I), h1, h2, fun X => ?_⟩
  rw [hl X, e1 X, e2 X, hM, hM, one_mul]; have hinv : -(e / 2) * (-(2 * e)) = 1 := by linear_combination he
  set z := (fi * d.cw w X) k.1 k.2.1
  split_ifs
  · conv_lhs => rw [show z = (z.re : ℂ) + Complex.I * ((-Complex.I * z).re : ℂ) from Complex.ext (by simp) (by simp)]
    linear_combination (-(z.re : ℂ) - Complex.I * ((-Complex.I * z).re : ℂ)) * hinv
  · rw [show star z = (z.re : ℂ) - Complex.I * ((-Complex.I * z).re : ℂ) from Complex.ext (by simp) (by simp)]
    linear_combination (-(z.re : ℂ) + Complex.I * ((-Complex.I * z).re : ℂ)) * hinv
private def TK (d : SD_k σ) : Submodule ℂ (M1 d → ℂ) := (kfS d).map (Tl d)
private theorem mul_pol {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (Q : PX d.m d.n) {f : M1 d → ℂ}
    (hf : f ∈ TK d) : (fun X => evX Q (R.loc w X) * f X) ∈ TK d := by
  induction Q using MvPolynomial.induction_on generalizing f with
  | C a => convert Submodule.smul_mem _ a hf using 1; funext _; simp [evX]
  | add p q hp hq => convert add_mem (hp hf) (hq hf) using 1; funext _; simp [evX, add_mul]
  | mul_X p k hp =>
    rw [show (fun X => evX (p * MvPolynomial.X k) (R.loc w X) * f X) =
      fun X => evX (MvPolynomial.X k) (R.loc w X) * (evX p (R.loc w X) * f X) from funext fun _ => by
        simp only [evX, map_mul]; ring]
    obtain ⟨Φ, hΦ, hΦe⟩ := hp hf; obtain ⟨Z₁, Z₂, c₁, c₂, h1, h2, e⟩ := var_span' R w k
    have hΦs : Φ ∈ d.sch := let ⟨_, _, h0, h1, _⟩ := hΦ; h0 h1
    have hc : cI ≠ 0 := by simp [cI, Real.pi_ne_zero, Complex.I_ne_zero]
    refine ⟨(c₁ / cI) • Box.D (d.dd.e (Z₁ * (dg d)ᵀ)) Φ + (c₂ / cI) • Box.D (d.dd.e (Z₂ * (dg d)ᵀ)) Φ,
      add_mem (Submodule.smul_mem _ _ (D_kfS (at_mul' h1 _) hΦ)) (Submodule.smul_mem _ _ (D_kfS (at_mul' h2 _) hΦ)),
      funext fun X => ?_⟩
    change d.T _ X = _ * (fun X => evX p (R.loc w X) * f X) X
    rw [← hΦe]; change d.T _ X = _ * d.T Φ X
    rw [T_add, T_smul, T_smul, T_D_dg hΦs h1, T_D_dg hΦs h2, e X]; field_simp
private theorem vac_mem {d : SD_k σ} (hT : TAll_k) (hF : FockMem_k) (R : RD_k d) {g : FinFn d} (hg : g ∈ SB _) :
    vacF R g ∈ TK d := by
  have hgen : vacF R g ∈ R.fock := Submodule.subset_span ⟨fun _ => 1, g, hg, funext fun _ => by simp [vacF, fP, evX]⟩
  obtain ⟨Φ, hΦ, e⟩ := (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 hgen)
  refine ⟨Φ, vac_kfS (thA R) (thB d R.ε) (fun _ hk w => commute_thB R hk w) (fun _ => 1) hΦ fun u u' hu hu' hr => ?_, e⟩
  refine sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (sub_mem (Box.DP_mem hΦ _ _) (Submodule.smul_mem _ _ (Box.DP_mem hΦ _ _)))
    (funext fun X => ?_))
  have t := congrFun ((Tl d).map_sub (Box.D (d.dd.e u') Φ) (Complex.I • Box.D (d.dd.e u) Φ)) X
  simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at t
  change d.T _ X = d.T _ X - Complex.I * d.T _ X at t; rw [t, vac_rel R g hΦ e hu hu' hr X, sub_self]; rfl
private theorem polyKFin_loc : TAll_k → FockMem_k → PolyKFin_k := fun hT hF F E _ _ _ _ _ σ d R Φ hΦ hf => by
  have hle : R.fock ≤ TK d := Submodule.span_le.2 fun _ ⟨P, g, hg, hEq⟩ => by
    rw [SetLike.mem_coe, hEq, show (fun X => (∏ w ∈ Finset.univ, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) =
      fun X => (∏ w ∈ Finset.univ, evX (P w) (R.loc w X)) * vacF R g X from funext fun _ => by
        simp only [fP, vacF, Finset.prod_mul_distrib]; ring]
    have hprod : ∀ s : Finset (InfinitePlace F), {f : M1 d → ℂ} → f ∈ TK d →
        (fun X => (∏ w ∈ s, evX (P w) (R.loc w X)) * f X) ∈ TK d := fun s => by
      induction s using Finset.induction_on with
      | empty => intro _ h; simpa using h
      | insert w s hw ih =>
        intro f hf; rw [show (fun X => (∏ w' ∈ insert w s, evX (P w') (R.loc w' X)) * f X) =
          fun X => evX (P w) (R.loc w X) * ((∏ w' ∈ s, evX (P w') (R.loc w' X)) * f X) from funext fun _ => by
            rw [Finset.prod_insert hw, mul_assoc]]; exact mul_pol R w (P w) (ih hf)
    exact hprod Finset.univ (vac_mem hT hF R hg)
  obtain ⟨Φ', ⟨N, _, h0, h1, h2⟩, e⟩ := hle hf
  rw [KFock.T_inj_k hT.1 d hΦ (h0 h1) e.symm]
  exact ⟨h0 h1, Submodule.finiteDimensional_of_le (S₂ := N)
    (Submodule.span_le.2 fun _ ⟨k, hk⟩ => hk ▸ h2 k.1 k.2 Φ' h1)⟩
end PolyKFin

theorem Fin.siegelWeilStd_k : SiegelWeilStd_k := by
  have hTT : TTheta_k := Tpar.tTheta_of_k (tweyl.tthetaComm_k TBij_k.tBij)
  have hW : TWeyl_k := TW.tWeyl_of_k TBij_k.tBij hTT (TW.UpToPf.upTo_of_k uniq_loc) poisson_loc TW.ThetaWPf.thetaW_k
  have hT : TAll_k := ⟨TBij_k.tBij, Tpar.tPar_k, hW, hTT,
    Tauto.thetaAuto_k _root_.GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary Tpar.tPar_k hTT⟩
  have hTC : ThetaCoef_k := Tauto.thetaCoef_k _root_.GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary TBij_k.tBij Tpar.tPar_k hTT
  have hA := kfour.auxiliaryExistence_holds; have hF := KFock.fockMem_k; have hLo := locOpEx_of_tAll_k hT
  have hLI : LocInst_k := KLI.locInst_of_k hT hA hF (KFock.liftEx_k hT.1)
  have hGS := KSplit.gSplit_of_k hF (KAway.awayAct_of_tAll_k hT)
  have hVK := vacK_loc hT hF hLo hLI (KAway.finAct_of_tAll_k hT)
  have hKP := KFP.kFinPoly_of_k hT Tunit.tUnit_k Tunit.tHeis_k hA hF hLo hLI
  have hPK := polyKFin_loc hT hF
  have hCT : CTSplit_k := Act.ctSplit_of_parts_k Act.indepDom_k Act.cptDom_k Act.absConv_k Act.firstEq_k
    (Act.secLaw_of_k (Act.secUnf_of_k Act.absConv_k))
  have hWk := KWhit.whitK_of_X_k KWhit.iwaRedC_k KWhit.W.pureSpan KWhit.W.linRedC KWhit.W.coreX KWhit.W.genDictX
    (fun _ _ _ _ _ _ _ _ d _ hΦ _ hk => KWhit.kfin_om_k d hΦ hk) hT hA Krd.rdEx_k hF hKP Khead.secK_k kunf.unfold_k
    whitGenLt hTC kfour.lamBd_k hPK
  have hWE := KWhit.whitEq_of_X_k KWhit.iwaRedC_k KWhit.W.pureSpan KWhit.W.linRedC KWhit.W.coreX KWhit.W.genDictX
    (fun _ _ _ _ _ _ _ _ d _ hΦ _ hk => KWhit.kfin_om_k d hΦ hk) hT hA Krd.rdEx_k hF hKP Khead.secK_k kunf.unfold_k
    Aeis.eisWk_k whitGenEq hTC kfour.lamBd_k hPK
  have hWL := KWhit.whitLow_of_X_k KWhit.iwaRedC_k KWhit.W.vacSpan KWhit.W.linRedC KWhit.W.coreX KWhit.W.genDictX
    hVK hT hA hF Khead.secK_k kunf.unfold_k Aeis.eisWk_k whitGenLow hTC kfour.lamBd_k hPK
  have hSt := AStep.stepOf_k HSt.holLeadB Holtb.holT hT hTC hA kfour.coefEx_k hF (KFock.liftEx_k hT.1) hLo hLI hGS
    hPK Khead.secK_k Aeis.eisWk_k kfour.lamBd_k (KSing.lamSing_of_k kfour.coefEx_k kfour.fourierZero_k Krd.denseW_k hA)
    kfour.fourierZero_k kunf.unfold_k hWL hVK (iwaQ_loc hT) hCT Afc.uEx_k (Afc.fcConj_of_k hA) Afc.orbRes_k
  exact Atop.siegelWeilStd_of_k AbsSt.absThm hT hTC hLo hLI hGS (KSplit.gIinv_of_k hT hF)
    (Kdil.gIdil_full_k hT hA hLo (KAway.awayAct_of_tAll_k hT) hLI) hKP hPK kunf.unfold_k hWk hWE
    AbsSt.vacuum_generates_polynomials (Ald.ldEx_of_k hT hA) hVK hSt
end PositivityTheory.SiegelWeilFormula
end
