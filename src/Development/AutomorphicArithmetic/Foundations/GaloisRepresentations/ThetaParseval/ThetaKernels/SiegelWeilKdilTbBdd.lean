module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Assembly
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Bridge
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Imports
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocAlg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocAlgPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocGaussPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocTop
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.SplitDomOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.WeightFactorEqAutomorphy
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.FrameBlockPairingSign
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DifferenceQuotientIsometryExchangeAlt
public import Development.WeilBound.ThetaLifts.FrameEstimates.FundamentalDomainFiniteVolume
public import Development.WeilBound.ThetaLifts.FrameEstimates.GrpTop
public import Development.WeilBound.ThetaLifts.FrameEstimates.SiegelAll
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinB
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinC
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinV
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Stab2CptK
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximal
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExtensionEmbeddingEvInfRealAd
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.CompactStandardSubgroup.KCptPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.FirstCountableGR
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.CharacterQuadraticDerivativeZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.CommuteOfUnitaryConjugate
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.FirstFrameHalfEqMul
public import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsRealStructure

/-! # SiegelWeilKdilTbBdd: Consolidated global theta-kernel definitions and proofs (SiegelWeilKdilTbBdd). -/
@[expose] public section
noncomputable section
open PositivityTheory.Rg.Sw.Glob (actZ gZf)
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open Finset (sum_congr)
open Real (exp)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section
namespace PositivityTheory.SiegelWeilFormula.Kdil
open PositivityTheory.SiegelWeilFormula
def ThetaBdd_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (d : SD_k σ), ∀ Fn ∈ d.schM, ∃ K : ℝ, ∀ h : UA σ d.A.J,
  Summable (fun X : d.ME => ‖Fn (mat h⁻¹ * incM F X)‖) ∧ ∑' X : d.ME, ‖Fn (mat h⁻¹ * incM F X)‖ ≤ K
namespace Tb
variable {σ : E →ₐ[F] E} (d : SD_k σ)
abbrev bA_k : Module.Basis (Fin 2) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) d.bs
abbrev Ix_k : Type := d.I3
theorem cmb_crd_k (Y : d.MxE) : d.cmb (d.crd Y) = Y := KFock.cmb_crd_k d Y
theorem crd_cmb_k (c : Ix_k d → AF F) : d.crd (d.cmb c) = c := KFock.crd_cmb_k d c
def mh_k (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) : Matrix (Ix_k d) (Ix_k d) (AF F) :=
  fun p q => if p.2.1 = q.2.1 then (bA_k d).repr (M p.1 q.1 * bA_k d q.2.2) p.2.2 else 0
theorem crd_mul_k (M : Matrix (Fin d.m) (Fin d.m) (AE F E)) (Y : d.MxE) :
    d.crd (M * Y) = mh_k d M *ᵥ d.crd Y := funext fun ⟨i, j, k⟩ => by
  have hY (i') : Y i' j = ∑ k', d.crd Y (i', j, k') • bA_k d k' := ((bA_k d).sum_repr (Y i' j)).symm
  show ((bA_k d).repr ((M * Y) i j)) k = _
  rw [Matrix.mul_apply, sum_congr rfl fun i' _ => by rw [hY i']]
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, mh_k, ite_mul, zero_mul,
    Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul]
  refine sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_eq_single j (fun _ _ hb => by simp [Ne.symm hb]) (fun h => absurd (Finset.mem_univ j) h)]
  simp only [ite_true]; exact sum_congr rfl fun _ _ => mul_comm _ _
theorem continuous_mh_k : Continuous (mh_k d) := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [mh_k]; split_ifs
  · exact (IsModuleTopology.continuous_of_linearMap ((bA_k d).coord p.2.2)).comp
      ((continuous_id.matrix_elem p.1 q.1).mul (continuous_const (y := bA_k d q.2.2)))
  · exact continuous_const
private theorem mulVec_ext {A B : Matrix (Ix_k d) (Ix_k d) (AF F)} (h : ∀ c, A *ᵥ c = B *ᵥ c) : A = B := by
  ext p q; simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single q 1)) p
private def mhU : GL (Fin d.m) (AE F E) →* GL (Ix_k d) (AF F) :=
  Units.map ⟨⟨mh_k d, mulVec_ext d fun c => by
      rw [← crd_cmb_k d c, ← crd_mul_k, Matrix.one_mul, crd_cmb_k, Matrix.one_mulVec]⟩,
    fun _ _ => mulVec_ext d fun c => by
      rw [← crd_cmb_k d c, ← crd_mul_k, Matrix.mul_assoc, crd_mul_k, crd_mul_k, crd_cmb_k, Matrix.mulVec_mulVec]⟩
private def xi : d.ME ≃ (Ix_k d → F) :=
  ⟨fun X p => d.bs.repr (X p.1 p.2.1) p.2.2, fun c i j => ∑ k, c (i, j, k) • d.bs k,
   fun X => funext fun i => funext fun j => d.bs.sum_repr (X i j),
   fun c => funext fun ⟨_, _, k⟩ => congrFun (d.bs.repr_sum_self fun k => c (_, _, k)) k⟩
theorem cpt_k (hS : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.ThK.Dbl.Cpt σ d.A.J := by
  have hC := cptAll_of_k PositivityTheory.ThKEst.grpTop_of _root_.PositivityTheory.ThKEst.epsOf_of_k
    (PositivityTheory.ThKEst.siegelAll_of hS) PositivityTheory.ThKEst.finVolU PositivityTheory.ThKF.unimodularity_holds
  rcases d.ok.sign with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hC F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inl h1) d.ok.aniso
  · exact hC F E σ d.B d.m d.A d.r d.s d.ok.good (Or.inr h1) d.ok.aniso
end Tb
theorem thetaBdd_of_k (hS : GlobalTheory.Published.SiegelSetUnitary) : ThetaBdd_k := by
  intro F E _ _ _ _ _ σ d Fn hF; obtain ⟨Ω, hΩ, cov⟩ := (Tb.cpt_k d hS).cov
  have hcmh : Continuous fun h : UA σ d.A.J => Tb.mhU d ((h : GL (Fin d.m) (AE F E))⁻¹) := by
    rw [Units.continuous_iff]
    refine ⟨(Tb.continuous_mh_k d).comp (Units.continuous_coe_inv.comp continuous_subtypeVal), ?_⟩
    simp only [← map_inv, inv_inv]; exact (Tb.continuous_mh_k d).comp (Units.continuous_val.comp continuous_subtypeVal)
  obtain ⟨u, hu, hb⟩ := _root_.GlobalTheory.CompanionTheory.EisRkNBound.exists_summable_bound_thetaC
    (hF : (fun c => Fn (d.cmb c)) ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := F) (ι := Tb.Ix_k d))
    (hΩ.image hcmh)
  have hcrdi (X : d.ME) : d.crd (incM F X) = PositivityTheory.RgEis.ratV (Tb.xi d X) := funext fun ⟨i, j, k⟩ => by
    show ((Tb.bA_k d).repr ((1 : AF F) ⊗ₜ[F] X i j)) k = algebraMap F (AF F) (d.bs.repr (X i j) k)
    rw [Algebra.TensorProduct.basis_repr_tmul]; simp
  have hbd (h) (hh : h ∈ Ω) (X) : ‖Fn (mat h⁻¹ * incM F X)‖ ≤ u (Tb.xi d X) := by
    have e : Fn (mat h⁻¹ * incM F X) = Fn (d.cmb (((Tb.mhU d ((h : GL (Fin d.m) (AE F E))⁻¹) : GL (Tb.Ix_k d) (AF F)) :
        Matrix (Tb.Ix_k d) (Tb.Ix_k d) (AF F)) *ᵥ PositivityTheory.RgEis.ratV (Tb.xi d X))) := by
      rw [← hcrdi, ← Tb.cmb_crd_k d (mat h⁻¹ * incM F X), Tb.crd_mul_k]; rfl
    rw [e]; exact hb _ ⟨h, hh, rfl⟩ _
  refine ⟨∑' ξ, u ξ, fun h => ?_⟩
  obtain ⟨γ, hγ, hγΩ⟩ := cov h; obtain ⟨G, hG⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hγ)
  let e : d.ME ≃ d.ME := ⟨fun X => G.1 * X, fun X => (G⁻¹).1 * X,
    fun _ => by dsimp only; rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul],
    fun _ => by dsimp only; rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]⟩
  have he (X) : Fn (mat (γ * h)⁻¹ * incM F (e X)) = Fn (mat h⁻¹ * incM F X) := by
    have hm : mat (γ * h)⁻¹ = mat h⁻¹ * incM F (G⁻¹).1 := by
      have : (((γ : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix _ _ _) = incM F (G⁻¹).1 := by
        rw [← hG, ← map_inv]; rfl
      simp only [mat, mul_inv_rev, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]; rw [this]
    congr 1; simp only [e, Equiv.coe_fn_mk, hm]
    rw [Matrix.mul_assoc, show incM F (G⁻¹).1 * incM F (G.1 * X) = incM F ((G⁻¹).1 * (G.1 * X)) from
      Matrix.map_mul.symm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have key (X) : ‖Fn (mat h⁻¹ * incM F X)‖ = ‖Fn (mat (γ * h)⁻¹ * incM F (e X))‖ := congrArg norm (he X).symm
  have hs : Summable (fun Y => ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hbd _ hγΩ) ((Tb.xi d).summable_iff.2 hu)
  refine ⟨(e.summable_iff.2 hs).congr fun X => (key X).symm, ?_⟩
  simp_rw [key]; rw [e.tsum_eq (fun Y => ‖Fn (mat (γ * h)⁻¹ * incM F Y)‖)]
  exact (hs.tsum_le_tsum (hbd _ hγΩ) ((Tb.xi d).summable_iff.2 hu)).trans_eq ((Tb.xi d).tsum_eq u)

namespace W
variable {σ : E →ₐ[F] E}
private theorem abs_tw {d : SD_k σ} (R : RD_k d) {w : InfinitePlace F} :
    |2 * Real.pi * ((R.sg w : ℤ) : ℝ)| = 2 * Real.pi := by
  rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h, abs_of_pos Real.pi_pos]
section LocFam
open Matrix
variable {d : SD_k σ} (R : RD_k d) {w : InfinitePlace F} {L : GR d.n → d.LF → d.LF}
  (hT : TAll_k) (hG : GoodAwayEx_k) (hFP : FPSw) (hL : R.IsLocOp w L)
include hT hG hFP hL
private theorem fam_eq_L (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (s : ℝ) :
    L (a s) (fP 1) = fun v => fam d.m X s v := by
  obtain ⟨k, hk⟩ := R.locOp_mM_law w hT hG hL
  set A : d.Mnc := diagonal fun j => (exp (s * X j) : ℂ) with hA
  have hdet : A.det = ((exp (∑ j, s * X j) : ℝ) : ℂ) := by rw [hA, det_diagonal, Real.exp_sum, Complex.ofReal_prod]
  have hpos : 0 < exp (∑ j, s * X j) := Real.exp_pos _
  have hunit : IsUnit A.det := by rw [hdet]; exact isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hpos.ne')
  have hinv : (Aᴴ)⁻¹ = diagonal fun j => (exp (-(s * X j)) : ℂ) := by
    rw [hA, diagonal_conjTranspose]; refine Matrix.inv_eq_left_inv (by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add,
        neg_add_cancel, Real.exp_zero, Complex.ofReal_one])
  rw [hk (a s) A hunit (by rw [ha s, mLoc, hinv]) (fP 1) (hFP d.m d.n 1)]; funext v
  have hn : ‖A.det‖ = exp (∑ j, s * X j) := by rw [hdet, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  rw [hn, ← hdet, div_self hunit.ne_zero, _root_.one_zpow, one_mul, hdet]
  simp only [fam, fP, evX, map_one, one_mul, gs]; congr 1
  · rw [← Complex.ofReal_pow, ← Real.exp_natCast_mul, Complex.ofReal_exp]
    congr 1; push_cast; rw [Finset.mul_sum, Finset.mul_sum]; exact sum_congr rfl fun _ _ => by ring
  · congr 1; push_cast; rw [neg_mul]; congr 2
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
    erw [show (Matrix.of v * A) b j = v b j * ((Real.exp (s * X j) : ℝ) : ℂ) from by rw [hA, Matrix.mul_diagonal]; rfl]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Complex.ofReal_mul, mul_pow,
      Complex.ofReal_exp, ← Complex.exp_natCast_mul, mul_comm]; congr 2; push_cast; ring
variable {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ} (hLD :
  LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
  (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
include hLD hsL hρ
private theorem vac_law (y : GR d.n) :
    L y (fP 1) = fun u => F0 p q e y *
      gZf (fun _ : Fin d.m => true) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (2 * Real.pi) (actZ y (Complex.I • 1)) u := by
  obtain ⟨pp, k, hpp, hk, rfl⟩ := PositivityTheory.Rg.Sw.AbsSt.iwa d.n y
  obtain ⟨nb, ma, b, a, hb, ha, hnb, hma, hpe, hZ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Kdil.up_decomp_pf pp hpp
  obtain ⟨c, -, hcf⟩ := R.locOp_mM hT hG hL; have hsw1 := hFP d.m d.n 1
  have hk1 : L k (fP 1) = fun u => F0 p q e k * fP 1 u := by rw [hρ k 1 hk, hLD.kvac k hk, fP_smul_one]
  have hca : c a = F0 p q e ma := by
    have h1 := hLD.law 1 ma 1 (by rw [hma, mLoc, Matrix.toBlocks_fromBlocks₂₁])
    rw [mul_one, hsL, hsL, hcf ma a ha hma _ hsw1, R.locOp_one hT hG hL _ hsw1] at h1; beta_reduce at h1
    rw [fP_one_of _ (fun i j => by show ∑ k, (Matrix.of (0 : Fin d.m → Fin d.n → ℂ)) i k * a k j = 0; simp),
      fP_one_zero] at h1; simpa using h1
  have hF0 : F0 p q e (pp * k) = c a * F0 p q e k := by
    have m1 := ((PositivityTheory.Rg.Sw.AbsSt.mult d.n p q e).2 pp k hpp).1
    have m2 := ((PositivityTheory.Rg.Sw.AbsSt.mult d.n p q e).2 nb ma
      (by show (mR nb).toBlocks₂₁ = 0; rw [hnb, nU, Matrix.toBlocks_fromBlocks₂₁])).1
    rw [m1, hpe, m2, weight_factor_unipotent_one p q e nb b hnb, one_mul, hca]
  have hswk : IsSw (L k (fP 1)) := (hL k _ hsw1).1
  rw [R.locOp_mul hT hG hL pp k _ hsw1, hpe, R.locOp_mul hT hG hL nb ma _ hswk,
    R.locOp_nU hT hG hL nb b hb hnb _ (hL ma _ hswk).1, hcf ma a ha hma _ hswk, ← hpe, hF0, actZ_mul_K pp k hk, hZ, hk1]
  funext u; rw [gzf_eval (R.sg w) b a hb u]; ring_nf; rfl
private theorem gf_L_fam (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (y : GR d.n) (s : ℝ) :
    Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (m := d.m) X y s = L y (fun v => fam d.m X s v) := by
  rw [gf_real e p q _ X a ha y s, ← vac_law R hT hG hFP hL hLD hsL hρ (y * a s),
    R.locOp_mul hT hG hL y (a s) (fP 1) (hFP _ _ 1), fam_eq_L R hT hG hFP hL X a ha s]
private theorem der_nbar (hA : SiegelWeilDatumProperties) (hB : GfBound)
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s))
    (nbb : GR d.n) (c : d.Mnc) (hc : cᴴ = c) (hnbb : mR nbb = nbLoc c) (r : ℕ) :
    (fun v => iteratedDeriv r (fun z => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (m := d.m) X nbb z v) 0) =
      L nbb (fP ((dil (2 * Real.pi) X ^ r) 1)) := by
  obtain ⟨C, s', κ, ε, hs', hκ, h4, -, hconj, -, -⟩ := R.locOp_nbar hT hA hG hL
  obtain ⟨hhol, hcont, hbd⟩ := hB d.m d.n e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (abs_tw R)
  obtain ⟨N, δ, Cb, hN, hδ, hNb⟩ := hbd nbb 0 (fun _ => by simp [Real.pi_pos])
  obtain ⟨ρs, hρs, hss⟩ := strip_ball X
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.mem_nhds_iff.1
    ((continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hN)
  set rr := min ρ0 ρs; have hrr : 0 < rr := lt_min hρ0 hρs
  have hsub : Metric.ball (0 : ℂ) rr ⊆ strip X := (Metric.ball_subset_ball (min_le_right _ _)).trans hss
  set Φ : ℂ → d.LF := fun z v => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X nbb z v
  have hΦd (v) : DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 rr) := (hhol nbb v).mono hsub
  have hΦc : ContinuousOn (fun zv : ℂ × (Fin d.m → Fin d.n → ℂ) => Φ zv.1 zv.2) (Metric.ball 0 rr ×ˢ Set.univ) :=
    cont_slice _ _ hcont nbb _ fun _ hzv => ⟨Set.mem_univ _, hsub hzv.1, Set.mem_univ _⟩
  have hΦb (z) (hz : z ∈ Metric.ball (0 : ℂ) rr) (v) : ‖Φ z v‖ ≤ Cb * Real.exp (-δ * sq v) := by
    simpa [sq, neg_mul] using hNb (nbb, z) (hball (Metric.ball_subset_ball (min_le_left _ _) hz)) (hsub hz) v
  have hC : C ≠ 0 := fun hC0 => by
    have h := congrFun (h4 _ (hFP d.m d.n 1)) 0
    simp only [locFT, hC0, zero_mul, Pi.smul_apply, smul_eq_mul, fP_one_zero, mul_one] at h; exact hκ h.symm
  set P : PX d.m d.n := (dil (2 * Real.pi) X ^ r) 1
  obtain ⟨hGc, hGi⟩ := sw_cont_int (hL nbb _ (hFP _ _ P)).1
  obtain ⟨-, -, -, hr9⟩ := _root_.PositivityTheory.SiegelWeilFormula.Kdil.hol_int_pf Φ rr Cb δ hrr hδ hΦd hΦc hΦb (kerFT s' 0) (kerFT_cont s' 0) (kerFT_norm s' 0)
  obtain ⟨-, hDc, C', hDb⟩ := hr9 r
  have hDi : Integrable (fun v => iteratedDeriv r (fun z => Φ z v) 0) :=
    Integrable.mono' ((_root_.PositivityTheory.SiegelWeilFormula.Kdil.gauss_int_pf δ hδ).const_mul C') hDc.aestronglyMeasurable (Filter.Eventually.of_forall hDb)
  have key (ξ : Fin d.m → Fin d.n → ℂ) : ∫ v, kerFT s' ξ v * iteratedDeriv r (fun z => Φ z v) 0 =
      ∫ v, kerFT s' ξ v * L nbb (fP P) v := by
    obtain ⟨ρ1, hρ1, hd1, hr1⟩ :=
      _root_.PositivityTheory.SiegelWeilFormula.Kdil.hol_int_pf Φ rr Cb δ hrr hδ hΦd hΦc hΦb (kerFT s' ξ) (kerFT_cont s' ξ) (kerFT_norm s' ξ)
    obtain ⟨ρ2, hρ2, hd2, hr2⟩ := _root_.PositivityTheory.SiegelWeilFormula.Kdil.fam_int_hol_pf d.m X (kerFT s' ξ) (kerFT_cont s' ξ) (kerFT_norm s' ξ)
    set ch : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) * ((Matrix.of ξ)ᴴ * Matrix.of ξ)))
    have hreal (s : ℝ) (_ : |s| < min ρ1 ρ2) :
        C * (∫ v, kerFT s' ξ v * Φ s v) = ch * (C * ∫ v, kerFT s' ξ v * fam d.m X s v) := by
      simp only [show ∀ v, Φ s v = L nbb (fun v => fam d.m X s v) v from
        fun v => congrFun (gf_L_fam R hT hG hFP hL hLD hsL hρ X a ha nbb s) v]
      have hsw : IsSw (fun v => fam d.m X s v) := by
        rw [← fam_eq_L R hT hG hFP hL X a ha s]; exact (hL (a s) (fP 1) (hFP _ _ 1)).1
      exact congrFun (hconj nbb c hc hnbb _ hsw) ξ
    have hid := _root_.PositivityTheory.SiegelWeilFormula.Kdil.iteratedDeriv_eq_of_real_pf (f := fun z => C * ∫ v, kerFT s' ξ v * Φ z v)
      (g := fun z => ch * (C * ∫ v, kerFT s' ξ v * fam d.m X z v)) (ρ := min ρ1 ρ2) (lt_min hρ1 hρ2)
      ((hd1.mono (Metric.ball_subset_ball (min_le_left _ _))).const_mul C)
      (((hd2.mono (Metric.ball_subset_ball (min_le_right _ _))).const_mul C).const_mul ch) hreal r
    rw [iteratedDeriv_const_mul', iteratedDeriv_const_mul', iteratedDeriv_const_mul'] at hid
    beta_reduce at hid; rw [(hr1 r).1, hr2 r] at hid; simp only [_root_.PositivityTheory.SiegelWeilFormula.Kdil.fam_deriv_pf] at hid
    exact mul_left_cancel₀ hC (hid.trans (congrFun (hconj nbb c hc hnbb _ (hFP _ _ P)) ξ).symm)
  have hint (ξ : Fin d.m → Fin d.n → ℂ) (g : d.LF) (hg : Integrable g) : Integrable (fun v => kerFT s' ξ v * g v) :=
    MeasureTheory.Integrable.bdd_mul hg (kerFT_cont s' ξ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => kerFT_norm s' ξ v)
  have hfin := _root_.PositivityTheory.SiegelWeilFormula.Kdil.ft_uniq_pf s' hs' (fun v => iteratedDeriv r (fun z => Φ z v) 0 - L nbb (fP P) v) (hDc.sub hGc)
    (hDi.sub hGi) fun ξ => by
      have h := key ξ; rw [← sub_eq_zero, ← integral_sub (hint ξ _ hDi) (hint ξ _ hGi)] at h
      simpa [kerFT, mul_sub] using h
  exact funext fun v => sub_eq_zero.1 (congrFun hfin v)
private theorem gf_der_big (hA : SiegelWeilDatumProperties) (hB : GfBound)
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (y : GR d.n) (hy : ((mR y).toBlocks₂₂).det ≠ 0)
    (r : ℕ) (u : Fin d.m → Fin d.n → ℂ) :
    iteratedDeriv r (fun z => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X y z u) 0 =
      L y (fP ((dil (2 * Real.pi) X ^ r) 1)) u := by
  obtain ⟨pp, nbb, c, hpp, hc, hnbb, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Kdil.dcell_pf y hy
  obtain ⟨nb', ma', b', a', hb', ha', hnb', hma', hpe', -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Kdil.up_decomp_pf pp hpp
  obtain ⟨cm, -, hcf⟩ := R.locOp_mM hT hG hL
  obtain ⟨hhol, -, -⟩ := hB d.m d.n e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (abs_tw R)
  obtain ⟨ρs, hρs, hss⟩ := strip_ball X
  set eb : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
    Matrix.trace (b' * ((Matrix.of u)ᴴ * Matrix.of u)))
  set w' : Fin d.m → Fin d.n → ℂ := fun i j => (Matrix.of u * a') i j
  have hform (f) (hf : IsSw f) : L (pp * nbb) f u = eb * (cm a' * L nbb f w') := by
    have h1 := (hL nbb f hf).1
    rw [R.locOp_mul hT hG hL pp nbb f hf, hpe', R.locOp_mul hT hG hL nb' ma' _ h1,
      R.locOp_nU hT hG hL nb' b' hb' hnb' _ (hL ma' _ h1).1, hcf ma' a' ha' hma' _ h1]; rfl
  have hreal (s : ℝ) (_ : |s| < ρs) : Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (pp * nbb) s u =
      eb * (cm a' * Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X nbb s w') := by
    rw [gf_L_fam R hT hG hFP hL hLD hsL hρ X a ha (pp * nbb) s, gf_L_fam R hT hG hFP hL hLD hsL hρ X a ha nbb s]
    have hsw : IsSw (fun v => fam d.m X s v) := by
      rw [← fam_eq_L R hT hG hFP hL X a ha s]; exact (hL (a s) (fP 1) (hFP _ _ 1)).1
    exact hform _ hsw
  have hid := _root_.PositivityTheory.SiegelWeilFormula.Kdil.iteratedDeriv_eq_of_real_pf
    (f := fun z => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (pp * nbb) z u)
    (g := fun z => eb * (cm a' * Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X nbb z w')) (ρ := ρs) hρs
    ((hhol _ u).mono hss) ((((hhol nbb w').mono hss).const_mul _).const_mul _) hreal r
  rw [hid, iteratedDeriv_const_mul', iteratedDeriv_const_mul']; beta_reduce
  have hdn := congrFun (der_nbar R hT hG hFP hL hLD hsL hρ hA hB X a ha nbb c hc hnbb r) w'
  beta_reduce at hdn; rw [hdn, hform _ (hFP _ _ _)]
end LocFam
end W

open W in
theorem gIdil_full_k (hT : TAll_k) (hAux : SiegelWeilDatumProperties) (hLE : LocOpEx_k) (hAw : AwayAct_k)
    (hLI : LocInst_k) : GIdil_k := by
  have hFP : FPSw := fun _ _ P => KFock.isSw_fP P
  intro F E _ _ _ _ _ σ d R w Ψ hΨ φ hφ g X a ha
  have hTPar := hT.2.1; have hTT := hT.2.2.2.1; have hTA := hT.2.2.2.2
  obtain ⟨hμ0, hμT, hTA'⟩ := hTA F E σ d; obtain ⟨L, hL⟩ := hLE F E σ d R w
  obtain ⟨x, y₀, hg, hx⟩ := KSplitW.decompW_k d R w g; obtain ⟨A, hA⟩ := hAw F E σ d R w x hx
  have hind : d.Indep w Ψ := ((KFock.fockMem_k F E σ d R).2.1 w Ψ hΨ).2; set Ψ' := A Ψ
  have hrep (Φ) (hΦ : Φ ∈ d.sch) (f) (hf : IsSw f) (hTΦ : d.T Φ = R.tens w f Ψ) (y) :
      d.T (d.om (g * R.ι w y) Φ) = R.tens w (L (y₀ * y) f) Ψ' := by
    obtain ⟨hLf, hLΦ⟩ := hL (y₀ * y) f hf; rw [hg, mul_assoc, ← map_mul, map_mul, mul_apply_eq_comp]
    exact (hA Ψ hind).2 _ hLf _ (d.om_sch _ _ hΦ) (hLΦ Ψ hind Φ hΦ hTΦ)
  have hmaj (δ : ℝ) (hδ : 0 < δ) : R.tens w (fun u => (Real.exp (-δ * sq u) : ℂ)) Ψ' ∈ d.schM := by
    obtain ⟨Φ, hΦ, hTΦ⟩ := KFock.liftSw1_k hT.1 d R w _ (isSw_gauss hδ) Ψ hΨ
    rw [← (hA Ψ hind).2 _ (isSw_gauss hδ) Φ hΦ hTΦ]; exact (hT.1 F E σ d).1 _ (d.om_sch x _ hΦ)
  obtain ⟨sL, ρ, p, q, e, -, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  obtain ⟨hhol, hcont, hbd0⟩ := gfBound d.m d.n e p q _ X (W.abs_tw R)
  set Gf' := Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X
  have hreal (y) (t : ℝ) : Gf' y (t : ℂ) = L (y * a t) (fP 1) := by
    simp only [Gf']; rw [gf_real e p q _ X a ha y t, ← W.vac_law R hT KFock.goodAwayEx_k hFP hL hLD hsL hρ (y * a t)]
  have hcont' (u) : ContinuousOn (fun q' : GR d.n × ℂ => Gf' q'.1 q'.2 u) (Set.univ ×ˢ strip X) :=
    cont_slice2 _ _ hcont u _ fun _ hq' => ⟨Set.mem_univ _, hq'.2, Set.mem_univ _⟩
  have hder (y) (hy : ((mR y).toBlocks₂₂).det ≠ 0) (r u) :
      iteratedDeriv r (fun z => Gf' y z u) 0 = L y (fP ((dil (2 * Real.pi) X ^ r) 1)) u :=
    W.gf_der_big R hT KFock.goodAwayEx_k hFP hL hLD hsL hρ hAux gfBound X a ha y hy r u
  obtain ⟨hUo, hUR, hUb⟩ := stripOK d.n X; have _ := matCount E d.m d.n
  set U := strip X; have h0U : (0 : ℂ) ∈ U := by simpa using hUR 0
  set Fm : GR d.n → ℂ → UA σ d.A.J → d.ME → ℂ :=
    fun y z h Xr => Gf' (y₀ * y) z (R.loc w (mat h⁻¹ * incM F Xr)) * Ψ' (mat h⁻¹ * incM F Xr) with hFm
  set ν : Measure (UA σ d.A.J) := (d.μ.restrict d.D Set.univ)⁻¹ • d.μ.restrict d.D
  have hc : (d.μ.restrict d.D Set.univ)⁻¹ ≠ ⊤ := by rw [ENNReal.inv_ne_top, Measure.restrict_apply_univ]; exact hμ0
  have : IsFiniteMeasure (d.μ.restrict d.D) := isFiniteMeasure_restrict.mpr hμT
  have hTP (Φ) (hΦ : Φ ∈ d.sch) (x h) :
      thetaSum F (d.om x (d.S h Φ)) = ∑' Xr, d.T (d.om x Φ) (mat h⁻¹ * incM F Xr) := by
    have hx' := d.om_sch x Φ hΦ
    rw [(hTT F E σ d Φ hΦ).2 x h, ← ((hTT F E σ d _ (d.ok.dbl.lin.pres h _ hx')).1).tsum_eq]
    exact tsum_congr fun Xr => (hTPar F E σ d _ hx').2.2 h (incM F Xr)
  have hI (Φ) (hΦ : Φ ∈ d.sch) (x) : d.I Φ x = ∫ h, ∑' Xr : d.ME, d.T (d.om x Φ) (mat h⁻¹ * incM F Xr) ∂ν := by
    show (⨍ h in d.D, thetaSum F (d.om x (d.S h Φ)) ∂d.μ) = _; simp_rw [hTP Φ hΦ x]; rfl
  have hT1 (P y') : d.T (d.om (g * R.ι w y') (φ P)) = R.tens w (L (y₀ * y') (fP P)) Ψ' :=
    hrep (φ P) (hφ P).1 (fP P) (hFP _ _ P) (hφ P).2 y'
  have hmulc : Continuous (fun q : GR d.n × ℂ => (y₀ * q.1, q.2)) :=
    (continuous_const.mul continuous_fst).prodMk continuous_snd
  obtain ⟨hHc, hHd, hHr⟩ := holMean (GR d.n) (UA σ d.A.J) d.ME ν U hUo hUb Fm
    (fun p _ _ => (hhol (y₀ * p) _).mul_const _)
    (fun h Xr => ((hcont' (R.loc w (mat h⁻¹ * incM F Xr))).comp (s := Set.univ ×ˢ U) hmulc.continuousOn
      (fun _ hq => ⟨trivial, hq.2⟩)).mul continuousOn_const)
    (fun p t _ => by
      have e : (fun h => ∑' k, Fm p t h k) = fun h => thetaSum F (d.om (g * R.ι w (p * a t)) (d.S h (φ 1))) :=
        funext fun h => by
          rw [hTP (φ 1) (hφ 1).1, hT1 1 (p * a t)]
          exact tsum_congr fun Xr => by rw [hFm]; dsimp only [RD_k.tens]; rw [hreal, mul_assoc]; rfl
      rw [e]; exact ((hTA' (φ 1) (hφ 1).1).1 _).aestronglyMeasurable.smul_measure _)
    (by
      rintro ⟨p, z⟩ ⟨-, hz⟩
      obtain ⟨N, δ, C, hN, hδ, hCb⟩ := hbd0 (y₀ * p) z hz
      obtain ⟨K, hK⟩ := thetaBdd_of_k _root_.GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary F E σ d _ (hmaj δ hδ)
      refine ⟨(fun q : GR d.n × ℂ => (y₀ * q.1, q.2)) ⁻¹' N, hmulc.continuousAt.preimage_mem_nhds hN,
        fun h Xr => |C| * ‖R.tens w (fun u => (Real.exp (-δ * sq u) : ℂ)) Ψ' (mat h⁻¹ * incM F Xr)‖,
        fun _ => |C| * K, fun h => (hK h).1.mul_left _, (integrable_const _).smul_measure hc,
        fun h => by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (hK h).2 (abs_nonneg C),
        fun q' hq' hq'U h Xr => ?_⟩
      have hb1 : ‖Gf' (y₀ * q'.1) q'.2 (R.loc w (mat h⁻¹ * incM F Xr))‖ ≤
          C * Real.exp (-δ * sq (R.loc w (mat h⁻¹ * incM F Xr))) := by
        simpa [sq, neg_mul] using hCb (y₀ * q'.1, q'.2) hq' hq'U (R.loc w (mat h⁻¹ * incM F Xr))
      simp only [hFm, RD_k.tens, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (hb1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)) (norm_nonneg _))
  clear_value Fm
  refine ⟨U, fun y z => ∫ h, ∑' k, Fm y z h k ∂ν, hUo, hUR, hHc, fun y => ⟨hHd y, fun t => ?_, fun r => ?_⟩⟩
  · beta_reduce; rw [hI (φ 1) (hφ 1).1, hT1 1 (y * a t)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun _ => tsum_congr fun _ => by
      rw [hFm]; dsimp only [RD_k.tens]; rw [hreal, mul_assoc])
  · have key (y') (hy' : ((mR (y₀ * y')).toBlocks₂₂).det ≠ 0) :
        iteratedDeriv r (fun z => ∫ h, ∑' k, Fm y' z h k ∂ν) 0 =
          d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y') := by
      rw [hHr y' 0 h0U r, hI _ (hφ _).1, hT1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun h => tsum_congr fun Xr => ?_)
      simp only [hFm, RD_k.tens]
      rw [iteratedDeriv_mul_const' (fun z => Gf' (y₀ * y') z (R.loc w (mat h⁻¹ * incM F Xr))) _ r]
      beta_reduce; rw [hder (y₀ * y') hy' r]
    have hcL : Continuous fun y' => iteratedDeriv r (fun z => ∫ h, ∑' k, Fm y' z h k ∂ν) 0 :=
      (derCont (GR d.n) U hUo (fun y' z => ∫ h, ∑' k, Fm y' z h k ∂ν) hHc hHd r).comp_continuous
        (continuous_id.prodMk continuous_const) (fun _ => ⟨trivial, h0U⟩)
    have hcR : Continuous fun y' => d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y') :=
      (hTA' _ (hφ _).1).2.1.comp (continuous_const.mul (R.cont w))
    exact congrFun (hcL.ext_on ((bigDense d.n).preimage (isOpenMap_mul_left y₀)) hcR key) y
end PositivityTheory.SiegelWeilFormula.Kdil
end

section
namespace PositivityTheory.SiegelWeilFormula.KK.W
open AddChar (map_zero_eq_one)
open Complex (I)
open Finset (mul_sum)
open Submodule (smul_mem)
variable {σ : E →ₐ[F] E}
abbrev M1 (d : SD_k σ) := d.MxE
abbrev M2 (d : SD_k σ) := Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)
abbrev M21 (d : SD_k σ) := Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E)
abbrev FinFn (d : SD_k σ) := d.Af3 → ℂ
abbrev trI (s : AF F) : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F s)
abbrev cI : ℂ := -(2 * Real.pi * I)
abbrev dg (d : SD_k σ) : M21 d := diagCols (Fin d.n)
abbrev c1 (d : SD_k σ) : M21 d := incM F d.b.1.toCols₁
abbrev c2 (d : SD_k σ) : M21 d := incM F d.b.1.toCols₂
abbrev sp (d : SD_k σ) (x y : M2 d) : AF F := symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) x y
abbrev mZ (d : SD_k σ) (Z X : M1 d) : ℝ := trI (sp d (X * (c2 d)ᵀ) (Z * (dg d)ᵀ))
def Tl (d : SD_k σ) : d.Fn →ₗ[ℂ] (M1 d → ℂ) := ⟨⟨d.T, KFock.T_add_k d⟩, KFock.T_smul_k d⟩
variable {d : SD_k σ}
theorem T_add (Φ Ψ : d.Fn) (X : M1 d) : d.T (Φ + Ψ) X = d.T Φ X + d.T Ψ X := congrFun (KFock.T_add_k d Φ Ψ) X
theorem T_smul (c : ℂ) (Φ : d.Fn) (X : M1 d) : d.T (c • Φ) X = c * d.T Φ X := congrFun (KFock.T_smul_k d c Φ) X
private theorem sp_eq (x y : M2 d) :
    sp d x y = (d.dd.e x).1 ⬝ᵥ (d.dd.e y).2 - (d.dd.e y).1 ⬝ᵥ (d.dd.e x).2 := d.dd.form x y
private theorem sp_anti (x y : M2 d) : sp d y x = -sp d x y := by rw [sp_eq, sp_eq]; ring
private theorem sp_smul_r (c : AF F) (x y : M2 d) : sp d x (c • y) = c * sp d x y := by
  rw [sp_eq, sp_eq, map_smul, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct,
    smul_eq_mul, smul_eq_mul, mul_sub]
private theorem sp_smul_l (c : AF F) (x y : M2 d) : sp d (c • x) y = c * sp d x y := by
  rw [sp_anti, sp_smul_r, sp_anti y x]; ring
private theorem sp_add_r (x y y' : M2 d) : sp d x (y + y') = sp d x y + sp d x y' := by
  rw [sp_eq, sp_eq, sp_eq, map_add (f := _), Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]; ring
private theorem rho_rho (v w : M2 d) (Φ : d.Fn) :
    d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ w Φ) =
      d.B.ψ (⅟(2 : AF F) * sp d v w) • d.dd.rho d.B.ψ (v + w) Φ := funext fun _ => by
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, map_add (f := _),
    Prod.fst_add, Prod.snd_add, add_assoc, add_dotProduct, dotProduct_add, sp_eq]
  congr 2; linear_combination (-((d.dd.e v).1 ⬝ᵥ (d.dd.e w).2)) * invOf_mul_self (2 : AF F)
private theorem rho_comm (v w : M2 d) (Φ : d.Fn) :
    d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ w Φ) = d.B.ψ (sp d v w) • d.dd.rho d.B.ψ w (d.dd.rho d.B.ψ v Φ) := by
  rw [rho_rho, rho_rho, smul_smul, add_comm w v, sp_anti v w, ← AddChar.map_add_eq_mul]
  congr 2; linear_combination (sp d v w) * invOf_mul_self (2 : AF F)
private theorem c2_iso : (c2 d)ᵀ * dbl (incM F d.Y.J) * (c2 d).map (cA σ) = 0 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have h0 : d.b.1.toCols₂ᵀ * dbl d.Y.J * d.b.1.toCols₂.map σ = 0 := Matrix.ext fun i j => by
    simpa [Matrix.mul_apply, Matrix.toCols₂, Matrix.map_apply, Matrix.transpose_apply] using
      congrFun₂ hε (Sum.inr i) (Sum.inr j)
  rw [c2, cA_incM, Krd.dbl_incM_k, incM_transpose, ← incM_mul', ← incM_mul', h0]; ext _ _; simp [incM]
private theorem sp_c2_iso (X Z : M1 d) : sp d (X * (c2 d)ᵀ) (Z * (c2 d)ᵀ) = 0 := by
  rw [sp, symp, Dense.hTens_tr,
    show (X * (c2 d)ᵀ)ᵀ * incM F d.A.J * (Z * (c2 d)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ =
        c2 d * (Xᵀ * incM F d.A.J * Z.map (cA σ) * ((c2 d).map (cA σ))ᵀ * (dbl (incM F d.Y.J))ᵀ) by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, map_cA_mul, ← Matrix.transpose_map]
      simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm,
    show (Xᵀ * incM F d.A.J * Z.map (cA σ) * ((c2 d).map (cA σ))ᵀ * (dbl (incM F d.Y.J))ᵀ) * c2 d =
        Xᵀ * incM F d.A.J * Z.map (cA σ) * ((c2 d)ᵀ * dbl (incM F d.Y.J) * (c2 d).map (cA σ))ᵀ by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc], c2_iso]; simp
private theorem T_tr_c2 (Φ : d.Fn) (Z : M1 d) (t : ℝ) (X : M1 d) :
    d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (c2 d)ᵀ)) Φ) X = d.T Φ (X + realAd F t • Z) := by
  simp only [SD_k.T]
  rw [rho_rho, sp_smul_r, sp_c2_iso, mul_zero, mul_zero, map_zero_eq_one, one_smul, ← Matrix.smul_mul, ← Matrix.add_mul]
private theorem T_rho_dg {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (Z : M1 d) (t : ℝ) (X : M1 d) :
    d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (dg d)ᵀ)) Φ) X =
      d.B.ψ (realAd F t * sp d (X * (c2 d)ᵀ) (Z * (dg d)ᵀ)) * d.T Φ X := by
  simp only [SD_k.T]; rw [rho_comm, map_smul, smul_eq_mul, sp_smul_r, ← Matrix.smul_mul]
  congr 1; exact d.ok.dbl.kill _ _ (GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ)
private theorem psi_line (s : AF F) (t : ℝ) : d.B.ψ (realAd F t * s) = Complex.exp (cI * ((t * trI s : ℝ) : ℂ)) := by
  rw [d.ok.good.std.2.2 _ (at_realAd_mul t s), tr_realAd_mul]
private theorem psi_line_deriv (s : AF F) : HasDerivAt (fun t : ℝ => d.B.ψ (realAd F t * s)) (cI * (trI s : ℂ)) 0 := by
  simp only [psi_line]; simpa using ((((hasDerivAt_id (0 : ℝ)).mul_const (trI s)).ofReal_comp).const_mul cI).cexp
private theorem l_D {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) {u : M2 d} (hu : At (evI F) u) (ha : Box.nf (d.dd.e u).1 ≠ 0) :
    HasDerivAt (fun t : ℝ => d.l (d.dd.rho d.B.ψ (realAd F t • u) Ψ)) (d.l (Box.D (d.dd.e u) Ψ)) 0 := by
  simp only [Darboux.rho, map_smul]
  have hw : At (evI F) (d.dd.e u) := fun s hs => by rw [← map_smul, hu s hs, map_zero]
  set w := d.dd.e u
  induction hΨ using Submodule.span_induction with
  | mem Φ hm =>
    obtain ⟨f, g, hg, rfl⟩ := hm; obtain ⟨G, hG, hD⟩ := Dense.hl_line_deriv (Box.nf w.1) (Dense.linForm (Box.nf w.2)) f
    obtain ⟨S, hS⟩ := d.ok.dbl.adm g hg
    have e (t : ℝ) : schr d.B.ψ (realAd F t • w) (pureA F f g) = pureA F (G t) g := funext fun z => by
      rw [← Box.pt_self z, Box.schr_pt d.ok.good.std hw, Dense.pureA_pt, hG]
      simp only [Dense.hl, Dense.pureA_pt, mul_assoc]
    simp only [e, hS]; rw [Box.D, Box.DP_pure, hS]; exact hD ha S
  | zero =>
    simp only [show ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (0 : d.Fn) = 0 from fun _ => funext fun _ => mul_zero _,
      map_zero, Box.D, Box.DP_zero]; exact hasDerivAt_const _ _
  | add x y hx hy ix iy =>
    simp only [show ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (x + y) =
      schr d.B.ψ (realAd F t • w) x + schr d.B.ψ (realAd F t • w) y from fun _ => funext fun _ => mul_add _ _ _,
      map_add (f := _)]; rw [Box.D, Box.DP_add hx hy, map_add (f := _)]; exact ix.add iy
  | smul c x hx ix =>
    simp only [show ∀ t : ℝ, schr d.B.ψ (realAd F t • w) (c • x) = c • schr d.B.ψ (realAd F t • w) x from
      fun _ => funext fun _ => mul_left_comm _ _ _, map_smul, smul_eq_mul]
    rw [Box.D, Box.DP_smul hx, map_smul, smul_eq_mul]; exact ix.const_mul c
private theorem D_zero (Φ : d.Fn) : Box.D (0 : (d.κ → AF F) × (d.κ → AF F)) Φ = 0 := by
  have h := Box.D_add_left (0 : (d.κ → AF F) × (d.κ → AF F)) 0 Φ; rw [add_zero] at h; simpa using h
private theorem rho_zero_line (Ψ : d.Fn) (u : M2 d) : d.dd.rho d.B.ψ (realAd F 0 • u) Ψ = Ψ :=
  funext fun _ => by simp [td_realAd_zero, Darboux.rho, schr]
private theorem rho_D {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {u : M2 d} (hu : At (evI F) u) (v : M2 d) :
    d.dd.rho d.B.ψ v (Box.D (d.dd.e u) Φ) =
      Box.D (d.dd.e u) (d.dd.rho d.B.ψ v Φ) + (cI * (trI (sp d v u) : ℂ)) • d.dd.rho d.B.ψ v Φ := by
  have hw : At (evI F) (d.dd.e u) := fun s hs => by rw [← map_smul, hu s hs, map_zero]
  have hΨ : d.dd.rho d.B.ψ v Φ ∈ d.sch := GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ
  funext z
  have h1 : HasDerivAt (fun t : ℝ => d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ (realAd F t • u) Φ) z)
      (d.dd.rho d.B.ψ v (Box.D (d.dd.e u) Φ) z) 0 := by
    simp only [Darboux.rho, schr, map_smul]; exact (Box.hasD d.ok.good.std hw hΦ _).const_mul _
  have h2 : HasDerivAt (fun t : ℝ => d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ (realAd F t • u) Φ) z)
      ((cI * (trI (sp d v u) : ℂ)) * d.dd.rho d.B.ψ v Φ z + 1 * Box.D (d.dd.e u) (d.dd.rho d.B.ψ v Φ) z) 0 := by
    rw [show (fun t : ℝ => d.dd.rho d.B.ψ v (d.dd.rho d.B.ψ (realAd F t • u) Φ) z) =
      fun t : ℝ => d.B.ψ (realAd F t * sp d v u) * d.dd.rho d.B.ψ (realAd F t • u) (d.dd.rho d.B.ψ v Φ) z from
      funext fun _ => by rw [rho_comm, sp_smul_r]; rfl]
    have h3 : HasDerivAt (fun t : ℝ => d.dd.rho d.B.ψ (realAd F t • u) (d.dd.rho d.B.ψ v Φ) z)
        (Box.D (d.dd.e u) (d.dd.rho d.B.ψ v Φ) z) 0 := by
      simpa only [Darboux.rho, map_smul] using Box.hasD d.ok.good.std hw hΨ z
    have h4 := (psi_line_deriv (d := d) (sp d v u)).mul h3
    rwa [rho_zero_line, td_realAd_zero, zero_mul, map_zero_eq_one] at h4
  rw [h1.unique h2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, add_comm]
private theorem T_D {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {u : M2 d} (hu : At (evI F) u) (ha : Box.nf (d.dd.e u).1 ≠ 0)
    (X : M1 d) : HasDerivAt (fun t : ℝ => d.T (d.dd.rho d.B.ψ (realAd F t • u) Φ) X)
      (d.T (Box.D (d.dd.e u) Φ) X) 0 := by
  set v := X * (c2 d)ᵀ
  have hΨ : d.dd.rho d.B.ψ v Φ ∈ d.sch := GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ
  rw [show (fun t : ℝ => d.T (d.dd.rho d.B.ψ (realAd F t • u) Φ) X) =
    fun t : ℝ => d.B.ψ (realAd F t * sp d v u) * d.l (d.dd.rho d.B.ψ (realAd F t • u) (d.dd.rho d.B.ψ v Φ)) from
    funext fun _ => by simp only [SD_k.T]; rw [rho_comm, sp_smul_r, map_smul, smul_eq_mul]]
  have h4 := (psi_line_deriv (d := d) (sp d v u)).mul (l_D hΨ hu ha)
  rw [rho_zero_line, td_realAd_zero, zero_mul, map_zero_eq_one] at h4; refine h4.congr_deriv ?_
  rw [show d.T (Box.D (d.dd.e u) Φ) X = d.l (d.dd.rho d.B.ψ v (Box.D (d.dd.e u) Φ)) from rfl, rho_D hΦ hu,
    map_add (f := _), map_smul, smul_eq_mul]; ring
private theorem vec_eq_zero {y : d.κ → AF F} (hy : At (evI F) y) (h0 : Box.nf y = 0) : y = 0 :=
  funext fun i => Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 (congrFun h0 i))
    (Dense.snd_eq_zero hy i)
private theorem eq_zero_of_nf {u : M2 d} (hu : At (evI F) u) (h1 : Box.nf (d.dd.e u).1 = 0)
    (h2 : Box.nf (d.dd.e u).2 = 0) : u = 0 := by
  have he : At (evI F) (d.dd.e u) := fun s hs => by rw [← map_smul, hu s hs, map_zero]
  rw [← d.dd.e.map_eq_zero_iff]
  exact Prod.ext (vec_eq_zero (fun c hc => congrArg Prod.fst (he c hc)) h1)
    (vec_eq_zero (fun c hc => congrArg Prod.snd (he c hc)) h2)
private theorem exists_at' (ξ : d.κ → mixedEmbedding.mixedSpace F) :
    ∃ v : M2 d, At (evI F) v ∧ d.dd.e v = (Dense.pt ξ 0, 0) :=
  ⟨d.dd.e.symm (Dense.pt ξ 0, 0), fun s hs => by
    rw [← map_smul, LinearEquiv.map_eq_zero_iff]; exact Prod.ext (Box.at_pt ξ s hs) (by simp),
    LinearEquiv.apply_symm_apply _ _⟩
theorem at_mul' {p : Type} [Fintype p] {Z : Matrix (Fin d.m) p (AE F E)} (hZ : At (evI F) Z) {q : Type}
    (N : Matrix p q (AE F E)) : At (evI F) (Z * N) := fun c hc => by rw [← Matrix.smul_mul, hZ c hc, Matrix.zero_mul]
theorem c1_eq_dg_mul : ∃ t : d.Mn, c1 d = dg d * t := by
  obtain ⟨t, ht⟩ := d.ok.frame.2; refine ⟨incM F t.1, ?_⟩
  ext i j; rw [Matrix.mul_apply]; change inclR (AF F) (d.b.1 i (Sum.inl j)) = _
  rw [show d.b.1 i (Sum.inl j) = ∑ k, (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) i k * t.1 k j
    from congrFun₂ ht i j, map_sum]
  refine sum_congr rfl fun k _ => ?_; rw [map_mul]; congr 1
  rcases i with i | i <;> · change inclR (AF F) ((1 : Matrix (Fin d.n) (Fin d.n) E) i k) = _
                            by_cases h : i = k <;> simp [dg, diagCols, Matrix.one_apply, h]
private theorem split_u (u : M2 d) :
    u = (u * (incM F (d.b⁻¹).1)ᵀ).toCols₁ * (c1 d)ᵀ + (u * (incM F (d.b⁻¹).1)ᵀ).toCols₂ * (c2 d)ᵀ := by
  have e : incM F d.b.1 = Matrix.fromCols (c1 d) (c2 d) := by
    rw [c1, c2, ← Matrix.fromCols_toCols d.b.1]; ext _ (_ | _) <;> rfl
  have e1 : (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Krd.bb_k d, Matrix.transpose_one]
  calc u = u * (incM F (d.b⁻¹).1)ᵀ * (incM F d.b.1)ᵀ := by rw [Matrix.mul_assoc, e1, Matrix.mul_one]
    _ = _ := by rw [e, Matrix.transpose_fromCols, ← Matrix.fromCols_toCols (u * (incM F (d.b⁻¹).1)ᵀ),
        Matrix.fromCols_mul_fromRows, Matrix.toCols₁_fromCols, Matrix.toCols₂_fromCols]
private theorem split_arch {u : M2 d} (hu : At (evI F) u) :
    ∃ Z₁ Z₂ : M1 d, At (evI F) Z₁ ∧ At (evI F) Z₂ ∧ u = Z₁ * (dg d)ᵀ + Z₂ * (c2 d)ᵀ := by
  obtain ⟨tA, htA⟩ := c1_eq_dg_mul (d := d); set W := u * (incM F (d.b⁻¹).1)ᵀ
  have hWa := at_mul' hu (incM F (d.b⁻¹).1)ᵀ
  refine ⟨W.toCols₁ * tAᵀ, W.toCols₂, at_mul' (at_toCols₁ hWa) tAᵀ, at_toCols₂ hWa, ?_⟩
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul, ← htA]; exact split_u u
private theorem c2_mul_inj {Z : M1 d} (h : Z * (c2 d)ᵀ = 0) : Z = 0 := by
  have e : incM F (d.b⁻¹).1.toRows₂ * c2 d = 1 := by
    rw [c2, ← incM_mul', show (d.b⁻¹).1.toRows₂ * d.b.1.toCols₂ = 1 from by
      ext i j; simpa [Matrix.mul_apply, Matrix.toRows₂, Matrix.toCols₂, Matrix.one_apply] using
        congrFun₂ (show (d.b⁻¹).1 * d.b.1 = 1 by simp) (Sum.inr i) (Sum.inr j)]
    ext i j; by_cases hij : i = j <;> simp [incM, Matrix.one_apply, hij]
  calc Z = Z * (incM F (d.b⁻¹).1.toRows₂ * c2 d)ᵀ := by rw [e, Matrix.transpose_one, Matrix.mul_one]
    _ = Z * (c2 d)ᵀ * (incM F (d.b⁻¹).1.toRows₂)ᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.zero_mul]
private theorem psi_quad_deriv (s : AF F) : HasDerivAt (fun t : ℝ => d.B.ψ (realAd F t * (realAd F t * s))) 0 0 := by
  simp only [show ∀ t : ℝ, d.B.ψ (realAd F t * (realAd F t * s)) = Complex.exp (cI * ((t * (t * trI s) : ℝ) : ℂ)) from
    fun t => by rw [psi_line, trI, tr_realAd_mul]]
  have h1 : HasDerivAt (fun t : ℝ => ((t * (t * trI s) : ℝ) : ℂ)) 0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_id (0 : ℝ)).mul_const (trI s))).ofReal_comp
  simpa using (h1.const_mul cI).cexp
private theorem T_D_dg_ne {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {Z : M1 d} (hZ : At (evI F) Z)
    (ha : Box.nf (d.dd.e (Z * (dg d)ᵀ)).1 ≠ 0) (X : M1 d) :
    d.T (Box.D (d.dd.e (Z * (dg d)ᵀ)) Φ) X = (cI * (mZ d Z X : ℂ)) * d.T Φ X :=
  (T_D hΦ (at_mul' hZ _) ha X).unique (by simp only [T_rho_dg hΦ]; exact (psi_line_deriv _).mul_const _)
private theorem T_sum_line {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (Z Z₀ X : M1 d) (t : ℝ) :
    d.B.ψ (realAd F t * (realAd F t * (⅟(2 : AF F) * sp d (Z * (dg d)ᵀ) (Z₀ * (c2 d)ᵀ)))) *
      d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (dg d)ᵀ + Z₀ * (c2 d)ᵀ)) Φ) X =
        d.B.ψ (realAd F t * sp d (X * (c2 d)ᵀ) (Z * (dg d)ᵀ)) * d.T Φ (X + realAd F t • Z₀) := by
  have hΦ' : d.dd.rho d.B.ψ (realAd F t • (Z₀ * (c2 d)ᵀ)) Φ ∈ d.sch :=
    GlobalTheory.HeisSchA.schr_mem_schA _ d.ok.good.std _ Φ hΦ
  rw [← T_tr_c2 Φ Z₀ t X, ← T_rho_dg hΦ' Z t X, rho_rho, T_smul, sp_smul_l, sp_smul_r, smul_add]; congr 2; ring
theorem T_D_dg {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {Z : M1 d} (hZ : At (evI F) Z) (X : M1 d) :
    d.T (Box.D (d.dd.e (Z * (dg d)ᵀ)) Φ) X = (cI * (mZ d Z X : ℂ)) * d.T Φ X := by
  by_cases ha : Box.nf (d.dd.e (Z * (dg d)ᵀ)).1 = 0; swap; · exact T_D_dg_ne hΦ hZ ha X
  have nfa (u v : M2 d) : Box.nf (d.dd.e (u + v)).1 = Box.nf (d.dd.e u).1 + Box.nf (d.dd.e v).1 := by
    rw [map_add (f := _), Prod.fst_add, Box.nf_add]
  by_cases hB : ∃ Z₀ : M1 d, At (evI F) Z₀ ∧ Box.nf (d.dd.e (Z₀ * (dg d)ᵀ)).1 ≠ 0
  · obtain ⟨Z₀, h0, h0'⟩ := hB
    have hs : Box.nf (d.dd.e ((Z + Z₀) * (dg d)ᵀ)).1 ≠ 0 := by rwa [Matrix.add_mul, nfa, ha, zero_add]
    have e1 := T_D_dg_ne hΦ (fun c hc => by rw [smul_add, hZ c hc, h0 c hc, add_zero]) hs X
    have e2 := T_D_dg_ne hΦ h0 h0' X
    have hm : mZ d (Z + Z₀) X = mZ d Z X + mZ d Z₀ X := by
      simp only [mZ, trI, Matrix.add_mul, sp_add_r, _root_.GlobalTheory.ThK.Dbl.Dense.evI_add, map_add (f := _)]
    rw [Matrix.add_mul, map_add (f := _), Box.D_add_left, T_add, e2, hm] at e1; push_cast at e1; linear_combination e1
  by_cases hC : ∃ Z₀ : M1 d, At (evI F) Z₀ ∧ Box.nf (d.dd.e (Z₀ * (c2 d)ᵀ)).1 ≠ 0
  · obtain ⟨Z₀, h0, h0'⟩ := hC; have hu := at_mul' hZ (dg d)ᵀ; have hu₀ := at_mul' h0 (c2 d)ᵀ
    have hs : Box.nf (d.dd.e (Z * (dg d)ᵀ + Z₀ * (c2 d)ᵀ)).1 ≠ 0 := by rwa [nfa, ha, zero_add]
    have h1 := T_D hΦ (fun c hc => by rw [smul_add, hu c hc, hu₀ c hc, add_zero]) hs X
    have h0d : HasDerivAt (fun t : ℝ => d.T Φ (X + realAd F t • Z₀)) (d.T (Box.D (d.dd.e (Z₀ * (c2 d)ᵀ)) Φ) X) 0 := by
      simpa only [T_tr_c2] using T_D hΦ hu₀ h0' X
    have hL := (psi_quad_deriv (d := d) (⅟(2 : AF F) * sp d (Z * (dg d)ᵀ) (Z₀ * (c2 d)ᵀ))).mul h1
    have hR := (psi_line_deriv (d := d) (sp d (X * (c2 d)ᵀ) (Z * (dg d)ᵀ))).mul h0d
    have E := (show HasDerivAt (fun t : ℝ => d.B.ψ (realAd F t * sp d (X * (c2 d)ᵀ) (Z * (dg d)ᵀ)) *
        d.T Φ (X + realAd F t • Z₀)) _ 0 by rw [← funext (T_sum_line hΦ Z Z₀ X)]; exact hL).unique hR
    rw [rho_zero_line] at E
    simp only [td_realAd_zero, zero_mul, map_zero_eq_one, zero_smul, add_zero, one_mul, zero_add] at E
    rw [map_add (f := _), Box.D_add_left, T_add] at E; simp only [mZ]; linear_combination E
  push Not at hB hC
  have hz (ξ : d.κ → mixedEmbedding.mixedSpace F) : ξ = 0 := by
    obtain ⟨v, hv, ev⟩ := exists_at' ξ; obtain ⟨Z₁, Z₂, h1, h2, rfl⟩ := split_arch hv
    have : Box.nf (d.dd.e (Z₁ * (dg d)ᵀ + Z₂ * (c2 d)ᵀ)).1 = ξ := by rw [ev]; exact Dense.evI_pt ξ 0
    rw [← this, nfa, hB Z₁ h1, hC Z₂ h2, add_zero]
  have hu0 : Z * (dg d)ᵀ = 0 := eq_zero_of_nf (at_mul' hZ (dg d)ᵀ) ha (hz _)
  have hm : mZ d Z X = 0 := by
    have hsp0 : sp d (X * (c2 d)ᵀ) 0 = 0 := by rw [sp_eq, map_zero]; simp
    simp only [mZ, trI, hu0, hsp0, show evI F (0 : AF F) = 0 from map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F),
      map_zero]
  have hD0 := D_zero (d := d) Φ
  rw [hm, hu0, map_zero, hD0, d.T_zero]; simp
private theorem hasDerivAt_c2 {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {Z : M1 d} (hZ : At (evI F) Z) (X : M1 d) :
    HasDerivAt (fun t : ℝ => d.T Φ (X + realAd F t • Z)) (d.T (Box.D (d.dd.e (Z * (c2 d)ᵀ)) Φ) X) 0 := by
  by_cases ha : Box.nf (d.dd.e (Z * (c2 d)ᵀ)).1 = 0
  swap; · simpa only [T_tr_c2] using T_D hΦ (at_mul' hZ _) ha X
  have hu := at_mul' hZ (c2 d)ᵀ
  by_cases hB : ∃ Z₀ : M1 d, At (evI F) Z₀ ∧ Box.nf (d.dd.e (Z₀ * (dg d)ᵀ)).1 ≠ 0
  · obtain ⟨Z₀, h0, h0'⟩ := hB; have hu₀ := at_mul' h0 (dg d)ᵀ
    have hs : Box.nf (d.dd.e (Z * (c2 d)ᵀ + Z₀ * (dg d)ᵀ)).1 ≠ 0 := by
      rwa [map_add (f := _), Prod.fst_add, Box.nf_add, ha, zero_add]
    have h1 := T_D hΦ (fun c hc => by rw [smul_add, hu c hc, hu₀ c hc, add_zero]) hs X
    have key (t : ℝ) : d.T Φ (X + realAd F t • Z) = d.B.ψ (realAd F t * -sp d (X * (c2 d)ᵀ) (Z₀ * (dg d)ᵀ)) *
        (d.B.ψ (realAd F t * (realAd F t * (⅟(2 : AF F) * sp d (Z₀ * (dg d)ᵀ) (Z * (c2 d)ᵀ)))) *
          d.T (d.dd.rho d.B.ψ (realAd F t • (Z * (c2 d)ᵀ + Z₀ * (dg d)ᵀ)) Φ) X) := by
      rw [add_comm (Z * (c2 d)ᵀ), T_sum_line hΦ Z₀ Z X t, ← mul_assoc, ← AddChar.map_add_eq_mul,
        mul_neg, neg_add_cancel, map_zero_eq_one, one_mul]
    have hR := (psi_line_deriv (d := d) (-sp d (X * (c2 d)ᵀ) (Z₀ * (dg d)ᵀ))).mul
      ((psi_quad_deriv (d := d) (⅟(2 : AF F) * sp d (Z₀ * (dg d)ᵀ) (Z * (c2 d)ᵀ))).mul h1)
    rw [funext key]; refine hR.congr_deriv ?_
    have e2 := T_D_dg_ne hΦ h0 h0' X; simp only [Pi.mul_apply]; rw [rho_zero_line]
    simp only [td_realAd_zero, zero_mul, map_zero_eq_one, one_mul, zero_add]
    rw [map_add (f := _), Box.D_add_left, T_add, e2, trI, evI_neg', map_neg]; simp only [mZ, trI]; push_cast; ring
  push Not at hB
  have he1 : At (evI F) (d.dd.e (Z * (c2 d)ᵀ)) := fun s hs => by rw [← map_smul, hu s hs, map_zero]
  have hsp (v) (hv : At (evI F) v) : sp d (Z * (c2 d)ᵀ) v = 0 := by
    obtain ⟨Z₁, Z₂, h1, -, rfl⟩ := split_arch hv
    have he2 : At (evI F) (d.dd.e (Z₁ * (dg d)ᵀ)) := fun s hs => by rw [← map_smul, at_mul' h1 _ s hs, map_zero]
    rw [sp_add_r, sp_c2_iso, add_zero, sp_eq, vec_eq_zero (fun c hc => congrArg Prod.fst (he1 c hc)) ha,
      vec_eq_zero (fun c hc => congrArg Prod.fst (he2 c hc)) (hB Z₁ h1)]; simp
  have h2 : Box.nf (d.dd.e (Z * (c2 d)ᵀ)).2 = 0 := funext fun j => by
    obtain ⟨v, hv, ev⟩ := exists_at' (d := d) (Pi.single j 1); have hzv := hsp v hv
    rw [sp_eq, ev, vec_eq_zero (fun c hc => congrArg Prod.fst (he1 c hc)) ha] at hzv
    simp only [dotProduct_zero, zero_sub, neg_eq_zero] at hzv
    have e3 := congrArg (evI F) hzv; rw [dotProduct, Dense.evI_sum] at e3; simp only [Dense.evI_mul] at e3
    simp only [show ∀ i, evI F (Dense.pt (Pi.single j (1 : mixedEmbedding.mixedSpace F)) 0 i) =
      (Pi.single j (1 : mixedEmbedding.mixedSpace F) : d.κ → mixedEmbedding.mixedSpace F) i from
      fun i => congrFun (Dense.evI_pt (Pi.single j (1 : mixedEmbedding.mixedSpace F)) 0) i] at e3
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)] at e3
    simpa [Box.nf, show evI F (0 : AF F) = 0 from map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)] using e3
  have hZ0 : Z = 0 := c2_mul_inj (eq_zero_of_nf hu ha h2); subst hZ0
  simp only [smul_zero, add_zero, Matrix.zero_mul, map_zero, D_zero (d := d), d.T_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _
theorem trace_sp (x y : M2 d) : trI (sp d x y) = ∑ w, -(2 * (Matrix.trace
    ((x.map (piInf (d.B.emb w)))ᵀ * d.A.J.map (d.B.emb w).1 * (y.map (piInf (d.B.emb w))).map star *
      (dbl (d.Y.J.map (d.B.emb w).1))ᵀ)).re) := by
  have h := d.ok.good.cm; rw [trI, Dense.trace_evI h.1]; refine sum_congr rfl fun w _ => ?_
  have e : (y.map (cA σ)).map (piInf (d.B.emb w)) = (y.map (piInf (d.B.emb w))).map star :=
    Matrix.ext fun _ _ => Dense.piInf_cA h _ _
  have eJ : (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) = dbl (d.Y.J.map (d.B.emb w).1) := by
    rw [Krd.dbl_incM_k, td_map_incM]; ext (_ | _) (_ | _) <;> simp [dbl]
  rw [sp, symp, Dense.ext_trace h (d.B.emb w), Dense.piInf_cA h, neg_one_mul, map_neg, Dense.hTens_tr,
    AddMonoidHom.map_trace (piInf (d.B.emb w)), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
    Matrix.transpose_map, Matrix.transpose_map, td_map_incM, eJ, e]; simp; ring
def kfS (d : SD_k σ) : Submodule ℂ d.Fn where
  carrier := {Φ | ∃ N : Submodule ℂ d.Fn, FiniteDimensional ℂ N ∧ N ≤ d.sch ∧ Φ ∈ N ∧ ∀ k ∈ d.K, ∀ Ψ ∈ N, d.om k Ψ ∈ N}
  zero_mem' := ⟨⊥, inferInstance, bot_le, zero_mem _,
    fun _ _ _ hg => by rw [(Submodule.mem_bot ℂ).1 hg, map_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro _ _ ⟨N, _, h0, h1, h2⟩ ⟨N', _, h0', h1', h2'⟩
    refine ⟨N ⊔ N', inferInstance, sup_le h0 h0', Submodule.add_mem_sup h1 h1', fun k hk _ hg => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hg
    rw [map_add (f := _)]; exact Submodule.add_mem_sup (h2 k hk x hx) (h2' k hk y hy)
  smul_mem' := fun c _ ⟨N, h, h0, h1, h2⟩ => ⟨N, h, h0, N.smul_mem c h1, h2⟩
section CompactK
attribute [local instance] GlobalTheory.ThK.Dbl.St.ae_ring GlobalTheory.ThK.Dbl.St.ae_t2 GlobalTheory.ThK.Dbl.St.ae_smul
private theorem isCompact_K (d : SD_k σ) : IsCompact (d.K : Set d.G) :=
  GlobalTheory.CompanionTheory.StdK.isCompact_of_isStdK d.B d.ok.good.cm d.b d.K d.ok.stdK
end CompactK
def thB (d : SD_k σ) (ε : ℤˣ) (w : InfinitePlace F) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ :=
  d.b.1.map (d.B.emb w).1 * (jE d.n ε)ᵀ * (d.b⁻¹).1.map (d.B.emb w).1
def thA (R : RD_k d) (w : InfinitePlace F) : Matrix (Fin d.m) (Fin d.m) ℂ :=
  (-(I * ((((R.ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * R.ζ))) • 1
theorem frame_form (R : RD_k d) (w : InfinitePlace F) :
    (d.b.1.map (d.B.emb w).1)ᵀ * dbl (d.Y.J.map (d.B.emb w).1) * (d.b.1.map (d.B.emb w).1).map star = jE d.n R.ε := by
  have cst (x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) : (x.map σ).map (d.B.emb w).1 =
      (x.map (d.B.emb w).1).map star := Matrix.ext fun i j => d.ok.good.cm.2.2.2 (d.B.emb w).1 (x i j)
  have hd : (dbl d.Y.J).map (d.B.emb w).1 = dbl (d.Y.J.map (d.B.emb w).1) := by
    ext (_ | _) (_ | _) <;> simp [dbl, Matrix.fromBlocks]
  have h1 := congrArg (fun x => x.map (d.B.emb w).1) R.hε
  simp only [Matrix.map_mul, Matrix.transpose_map, cst, hd] at h1
  rw [h1]; ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [jE, Matrix.fromBlocks, Matrix.smul_apply, hij]
theorem commute_thB (R : RD_k d) {k : d.G} (hk : k ∈ d.K) (w : InfinitePlace F) :
    Commute ((mat2 k).map (piInf (d.B.emb w))) (thB d R.ε w) := by
  have e1 : d.b.1.map (d.B.emb w).1 * (d.b⁻¹).1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : (d.b⁻¹).1.map (d.B.emb w).1 * d.b.1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMk : (inFrame d.b k).map (piInf (d.B.emb w)) =
      (d.b⁻¹).1.map (d.B.emb w).1 * (mat2 k).map (piInf (d.B.emb w)) * d.b.1.map (d.B.emb w).1 := by
    rw [inFrame, Matrix.map_mul, Matrix.map_mul, map_incM', map_incM']
  have hDw : (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) = dbl (d.Y.J.map (d.B.emb w).1) := by
    rw [Krd.dbl_incM_k, map_incM']; ext (_ | _) (_ | _) <;> simp [dbl, Matrix.fromBlocks]
  have hk2 : ((mat2 k).map (piInf (d.B.emb w)))ᵀ * (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) *
      ((mat2 k).map (piInf (d.B.emb w))).map star = (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) := by
    have cstA (x : d.Mn2) : (x.map (cA σ)).map (piInf (d.B.emb w)) = (x.map (piInf (d.B.emb w))).map star :=
      Matrix.ext fun i j => Dense.piInf_cA d.ok.good.cm (d.B.emb w) (x i j)
    simpa only [mat2, Matrix.map_mul, Matrix.transpose_map, cstA] using
      congrArg (fun x => x.map (piInf (d.B.emb w))) k.2
  exact commute_of_unitary_conjugate e1 e2 hMk (((d.ok.stdK k).1 hk).1 w) (hDw.symm ▸ frame_form R w) hk2
def vacF (R : RD_k d) (g : FinFn d) (X : M1 d) : ℂ :=
  (∏ w, gs (2 * Real.pi) (R.loc w X)) * g fun k => (d.crd X k).2
private def qL (R : RD_k d) (X Z : M1 d) (t : ℝ) : ℝ :=
  ∑ w, ∑ a, ∑ i, ‖(((R.fr w)⁻¹).1 * d.cw w X) a i + (t : ℂ) * (((R.fr w)⁻¹).1 * d.cw w Z) a i‖ ^ 2
section
variable (R : RD_k d)
private theorem vacF_line (g : FinFn d) (X Z : M1 d) (t : ℝ) :
    vacF R g (X + realAd F t • Z) = Complex.exp ((-(2 * Real.pi) * qL R X Z t : ℝ) : ℂ) * g fun k => (d.crd X k).2 := by
  have hcw (w) : d.cw w (X + realAd F t • Z) = d.cw w X + (t : ℂ) • d.cw w Z := Matrix.ext fun i j => by
    show piInf (d.B.emb w) ((X + realAd F t • Z) i j) = piInf (d.B.emb w) (X i j) + (t : ℂ) * piInf (d.B.emb w) (Z i j)
    rw [Matrix.add_apply, Matrix.smul_apply, map_add (f := _),
      GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul]
  have hcrd (k) : (d.crd (X + realAd F t • Z) k).2 = (d.crd X k).2 := by
    have e : d.crd (X + realAd F t • Z) k = d.crd X k + realAd F t * d.crd Z k := by
      simp only [SD_k.crd, Matrix.add_apply, Matrix.smul_apply, map_add (f := _), map_smul, Finsupp.add_apply,
        Finsupp.smul_apply, smul_eq_mul]
    rw [e, snd_add_realAd]
  simp only [vacF, hcrd, gs, RD_k.loc, hcw, Matrix.mul_add, Matrix.mul_smul, Matrix.map_apply, norm_star,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  congr 1; rw [← Complex.exp_sum]; congr 1
  rw [qL]; push_cast; rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
private theorem vacF_deriv (g : FinFn d) (X Z : M1 d) :
    HasDerivAt (fun t : ℝ => vacF R g (X + realAd F t • Z))
      (((-(4 * Real.pi) * ∑ w, (Matrix.trace ((((R.fr w)⁻¹).1 * d.cw w X)ᴴ *
        (((R.fr w)⁻¹).1 * d.cw w Z))).re : ℝ) : ℂ) * vacF R g X) 0 := by
  rw [funext (vacF_line R g X Z)]
  have hq : HasDerivAt (qL R X Z)
      (∑ w, ∑ a, ∑ i, 2 * (star ((((R.fr w)⁻¹).1 * d.cw w X) a i) * (((R.fr w)⁻¹).1 * d.cw w Z) a i).re) 0 :=
    HasDerivAt.fun_sum fun _ _ => HasDerivAt.fun_sum fun _ _ => HasDerivAt.fun_sum fun _ _ => hasDerivAt_normSq _ _
  refine (((hq.const_mul (-(2 * Real.pi))).ofReal_comp.cexp).mul_const (g fun k => (d.crd X k).2)).congr_deriv ?_
  have e0 : vacF R g X = Complex.exp ((-(2 * Real.pi) * qL R X Z 0 : ℝ) : ℂ) * g fun k => (d.crd X k).2 := by
    simpa [_root_.PositivityTheory.SiegelWeilFormula.KK.td_realAd_zero] using vacF_line R g X Z 0
  rw [e0]; simp only [trace_re, ← mul_sum]; push_cast; ring
private theorem T_D_vac (g : FinFn d) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hT : d.T Φ = vacF R g)
    {u : M2 d} (hu : At (evI F) u) (X : M1 d) :
    d.T (Box.D (d.dd.e u) Φ) X = (∑ w, Sw (d.A.J.map (d.B.emb w).1) ((R.fr w)⁻¹).1 (dbl (d.Y.J.map (d.B.emb w).1))
      (d.b.1.map (d.B.emb w).1) ((d.b⁻¹).1.map (d.B.emb w).1) (d.cw w X) (d.cw w u)) * vacF R g X := by
  obtain ⟨tA, htA⟩ := c1_eq_dg_mul (d := d); set W := u * (incM F (d.b⁻¹).1)ᵀ with hW
  have hWa : At (evI F) W := at_mul hu _
  have e1 : W.toCols₁ * (c1 d)ᵀ = (W.toCols₁ * tAᵀ) * (dg d)ᵀ := by rw [htA, Matrix.transpose_mul, Matrix.mul_assoc]
  have hs := split_u u; rw [← hW, e1] at hs
  have hder := hasDerivAt_c2 hΦ (at_toCols₂ hWa) X; rw [hT] at hder
  rw [show Box.D (d.dd.e u) Φ = Box.D (d.dd.e ((W.toCols₁ * tAᵀ) * (dg d)ᵀ)) Φ + Box.D (d.dd.e (W.toCols₂ * (c2 d)ᵀ)) Φ
    from by conv_lhs => rw [hs]; rw [map_add (f := _), Box.D_add_left], T_add, T_D_dg hΦ (at_mul (at_toCols₁ hWa) tAᵀ),
    hT, (vacF_deriv R g X W.toCols₂).unique hder |>.symm]
  have mapT {p q r : Type} [Fintype q] (w : InfinitePlace F) (x : Matrix p q (AE F E)) (y : Matrix r q E) :
      (x * (incM F y)ᵀ).map (piInf (d.B.emb w)) = x.map (piInf (d.B.emb w)) * (y.map (d.B.emb w).1)ᵀ := by
    rw [Matrix.map_mul, Matrix.transpose_map, map_incM']
  have hmW (w) : W.map (piInf (d.B.emb w)) = d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ := by rw [hW, mapT]; rfl
  have hm : mZ d (W.toCols₁ * tAᵀ) X = ∑ w, -(2 * (T1 (d.A.J.map (d.B.emb w).1) (dbl (d.Y.J.map (d.B.emb w).1))
      (d.b.1.map (d.B.emb w).1) (d.cw w X) ((d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₁)).re) := by
    rw [mZ, ← e1, trace_sp]; refine Finset.sum_congr rfl fun w _ => ?_
    rw [show (X * (c2 d)ᵀ).map (piInf (d.B.emb w)) = d.cw w X * ((d.b.1.map (d.B.emb w).1).toCols₂)ᵀ from
          by rw [mapT]; rfl,
      show (W.toCols₁ * (c1 d)ᵀ).map (piInf (d.B.emb w)) =
        (d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₁ * ((d.b.1.map (d.B.emb w).1).toCols₁)ᵀ from
          by rw [mapT, ← hmW]; rfl]; rfl
  rw [hm]; simp only [show ∀ w, d.cw w W.toCols₂ = (d.cw w u * ((d.b⁻¹).1.map (d.B.emb w).1)ᵀ).toCols₂ from
    fun w => by rw [← hmW]; rfl, Sw, T2, cI, Finset.sum_mul]; push_cast
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring
theorem vac_rel (g : FinFn d) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hT : d.T Φ = vacF R g)
    {u u' : M2 d} (hu : At (evI F) u) (hu' : At (evI F) u')
    (hr : Box.Rel d.B.emb (fun _ => 1) (thA R) (thB d R.ε) u u') (X : M1 d) :
    d.T (Box.D (d.dd.e u') Φ) X = I * d.T (Box.D (d.dd.e u) Φ) X := by
  rw [T_D_vac R g hΦ hT hu' X, T_D_vac R g hΦ hT hu X, ← mul_assoc, mul_sum]
  congr 1; refine sum_congr rfl fun w _ => ?_
  have e2 : (d.b⁻¹).1.map (d.B.emb w).1 * d.b.1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hfi : (R.fr w).1 * ((R.fr w)⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact Sw_rel e2 hfi (frame_form R w) (R.hfr w) R.hζ (d.cw w X) (d.cw w u) (d.cw w u') (hr w)
end
private theorem om_D (k : d.G) {u : M2 d} (hu : At (evI F) u) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) :
    d.om k (Box.D (d.dd.e u) Φ) = Box.D (d.dd.e (actB (cA σ) k u)) (d.om k Φ) := by
  have hs := d.ok.dbl.weil.2.1.toIsSplitting
  have himp : Box.Imp d.B.ψ (d.om k) fun w => d.dd.e (actB (cA σ) k (d.dd.e.symm w)) :=
    ⟨hs.pres k, hs.adm k, fun _ _ => by simp only [actB, map_add (f := _), Matrix.add_mul],
      fun _ _ => by simp only [actB, map_smul, Matrix.smul_mul], fun w φ hφ => by
        have := hs.impl k (d.dd.e.symm w) φ hφ; rwa [Darboux.rho, LinearEquiv.apply_symm_apply] at this⟩
  have h := himp.inter d.ok.good.std (Box.at_e d.dd.e hu) hΦ; rwa [LinearEquiv.symm_apply_apply] at h
theorem D_kfS {u : M2 d} (hu : At (evI F) u) {Φ : d.Fn} (h : Φ ∈ kfS d) : Box.D (d.dd.e u) Φ ∈ kfS d := by
  obtain ⟨N, _, h0, h1, h2⟩ := h; obtain ⟨N', _, h4⟩ := Box.exists_D_fin N h0
  refine ⟨Submodule.span ℂ {z | ∃ v, At (evI F) v ∧ ∃ x ∈ N, z = Box.D (d.dd.e v) x},
    Submodule.finiteDimensional_of_le (S₂ := N') (Submodule.span_le.2
      (by rintro _ ⟨_, -, _, hx, rfl⟩; exact h4 _ _ _ hx)),
    Submodule.span_le.2 (by rintro _ ⟨_, -, _, hx, rfl⟩; exact Box.DP_mem (h0 hx) _ _),
    Submodule.subset_span ⟨u, hu, Φ, h1, rfl⟩, fun k hk z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem _ hz => obtain ⟨v, hv, x, hx, rfl⟩ := hz
                exact Submodule.subset_span ⟨_, Box.at_actB k hv, _, h2 k hk x hx, om_D k hv (h0 hx)⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add _ _ _ _ i j => rw [map_add]; exact add_mem i j
  | smul _ _ _ i => rw [map_smul]; exact smul_mem _ _ i
theorem vac_kfS (θ : InfinitePlace F → Matrix (Fin d.m) (Fin d.m) ℂ)
    (θ' : InfinitePlace F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ)
    (hc : ∀ k ∈ d.K, ∀ w, Commute ((mat2 k).map (piInf (d.B.emb w))) (θ' w)) (ε : InfinitePlace F → ℤˣ) {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : ∀ u u', At (evI F) u → At (evI F) u' → Box.Rel d.B.emb ε θ θ' u u' →
      Box.D (d.dd.e u') Φ = I • Box.D (d.dd.e u) Φ) : Φ ∈ kfS d := by
  have hs := d.ok.dbl.weil.2.1.toIsSplitting
  obtain ⟨Λ, l1, l2, s, s1, s2⟩ :=
    _root_.GlobalTheory.ThK.Dbl.finLevel_k F E σ d.B d.m d.n d.A d.Y d.ok.good d.κ d.dd d.K (isCompact_K d) Φ hΦ
  let N : Submodule ℂ d.Fn :=
    { carrier := {Ψ | Ψ ∈ d.sch ∧ (∀ u ∈ Λ, d.dd.rho d.B.ψ u Ψ = Ψ) ∧ ∀ u u', At (evI F) u → At (evI F) u' →
        Box.Rel d.B.emb ε θ θ' u u' → Box.D (d.dd.e u') Ψ = I • Box.D (d.dd.e u) Ψ}
      zero_mem' := ⟨zero_mem _, fun _ _ => funext fun _ => mul_zero _,
        fun _ _ _ _ _ => by simp only [Box.D, Box.DP_zero, smul_zero]⟩
      add_mem' := fun h h' => ⟨add_mem h.1 h'.1, fun u hu => by
        rw [show d.dd.rho d.B.ψ u (_ + _) = d.dd.rho d.B.ψ u _ + d.dd.rho d.B.ψ u _ from funext fun _ => mul_add _ _ _,
          h.2.1 u hu, h'.2.1 u hu], fun u u' a b c => by
        simp only [Box.D] at h h' ⊢
        rw [Box.DP_add h.1 h'.1, Box.DP_add h.1 h'.1, h.2.2 u u' a b c, h'.2.2 u u' a b c, smul_add]⟩
      smul_mem' := fun t _ h => ⟨smul_mem _ _ h.1, fun u hu => by
        rw [show d.dd.rho d.B.ψ u (t • _) = t • d.dd.rho d.B.ψ u _ from funext fun _ => mul_left_comm _ _ _,
          h.2.1 u hu], fun u u' a b c => by
        simp only [Box.D] at h ⊢; rw [Box.DP_smul h.1, Box.DP_smul h.1, h.2.2 u u' a b c, smul_comm]⟩ }
  refine ⟨N, ?_, fun _ h => h.1, ⟨hΦ, l2, hv⟩, fun k hk Ψ h => ⟨hs.pres k _ h.1, fun u hu => ?_, fun u u' a b c => ?_⟩⟩
  · refine FiniteDimensional.of_injective ((LinearMap.pi fun y : s => LinearMap.proj y.1) ∘ₗ N.subtype)
      ((injective_iff_map_eq_zero _).2 fun Ψ h0 => Subtype.ext (funext fun z => ?_))
    have sp' (x) (y : d.κ → AF F) (hy : ∀ i, evI F (y i) = 0) : Dense.pt x 0 + y = Dense.pt x (Box.fn y) := by
      rw [← Box.pt_self (Dense.pt x 0 + y), Box.nf_add, Box.nf_pt, show Box.nf y = 0 from funext hy, add_zero]
      exact congrArg (Dense.pt x) (funext fun _ => zero_add _)
    have z0 (i) : evI F (Dense.pt 0 (Box.fn z) i) = 0 := congrFun (Dense.evI_pt 0 (Box.fn z)) i
    have hpt := s2 Ψ.1 Ψ.2.2.1 (Dense.pt (Box.nf z) 0) (Box.at_pt _) (fun y hy => ?_) _ z0
    · rwa [sp' _ _ z0, show Box.fn (Dense.pt 0 (Box.fn z)) = Box.fn z from rfl, Box.pt_self] at hpt
    obtain ⟨f, e⟩ := Box.slice Ψ.2.1 (Box.fn y)
    have g : Box.Gs d.dd.e d.B.emb ε θ θ' f := fun u u' a b c => SchwartzMap.ext fun x => by
      have := congrFun (Ψ.2.2.2 u u' a b c) (Dense.pt x (Box.fn y))
      rwa [Pi.smul_apply, Box.D, Box.D, Box.DP_pt e, Box.DP_pt e] at this
    rw [sp' _ _ (s1 y hy), e]; by_cases hf : f = 0; · rw [hf]; rfl
    obtain ⟨_, hg⟩ := g.gau d.ok.good.cm hf; refine (hg.ne 0 ?_).elim
    rw [← e, ← show Box.nf y = 0 from funext (s1 y hy), Box.pt_self]; exact congrFun h0 ⟨y, hy⟩
  · rw [← Box.actB_inv k u, ← hs.impl k _ _ h.1, h.2.1 _ ((l1 u hu).2.2 _ (inv_mem hk))]
  · rw [← Box.actB_inv k u, ← Box.actB_inv k u', ← om_D k (Box.at_actB _ a) h.1,
      ← om_D k (Box.at_actB _ b) h.1, ← map_smul]
    refine congrArg (d.om k) (h.2.2 _ _ (Box.at_actB _ a) (Box.at_actB _ b) fun w => ?_)
    simp only [actB, Matrix.map_mul, Matrix.transpose_map, c w, Matrix.smul_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul]
    exact congrArg (fun x => _ • (_ * (_ * xᵀ))) (hc k⁻¹ (inv_mem hk) w).eq
end PositivityTheory.SiegelWeilFormula.KK.W
end
end
