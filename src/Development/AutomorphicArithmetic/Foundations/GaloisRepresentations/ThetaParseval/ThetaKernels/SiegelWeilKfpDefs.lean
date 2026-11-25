module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingGrp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Unfold0K
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DenseW
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.GoodAwayEx
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LiftExOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.PiProdSch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.ChiWPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepMA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FrameArchimedeanPairing
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.MemLpSchM
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.RotVac
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.LRhoOm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.UnitaryGroupInverseFormula
public import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss
public import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.CharacterQuadraticDerivativeZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-! # FockDecK: Preliminary helper declarations for global theta kernels. -/

@[expose] public section

theorem UpperTheory.Reformulated.B.Glb2.fock_dec_k :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {d : PositivityTheory.SiegelWeilFormula.SD_k σ} (R : PositivityTheory.SiegelWeilFormula.RD_k d)
      (w : NumberField.InfinitePlace F),
      ∀ f ∈ R.fock,
        ∃ (k : ℕ) (P : Fin k → PositivityTheory.Rg.Sw.PX d.m d.n) (Ψ : Fin k → PositivityTheory.SiegelWeilFormula.Mx F E d.m d.n → ℂ),
          (∀ (i : Fin k), Ψ i ∈ R.away w) ∧ f = ∑ i : Fin k, R.tens w (PositivityTheory.SiegelWeilFormula.fP (P i)) (Ψ i) := by
  intro F E _ _ _ _ _ σ d R w f hf
  obtain ⟨k, c, u, rfl⟩ := Submodule.mem_span_set'.1 hf
  choose P g hg hu using fun i => (u i).2
  refine ⟨k, fun i => P i w, fun i => c i • _, fun i => Submodule.smul_mem _ (c i)
    (Submodule.subset_span ⟨P i, g i, hg i, rfl⟩), Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hu i]
  funext X
  simp only [PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm (PositivityTheory.SiegelWeilFormula.fP _ _), ← mul_assoc (PositivityTheory.SiegelWeilFormula.fP _ _),
    @Finset.mul_prod_erase _ _ _ (_) _ (fun v => PositivityTheory.SiegelWeilFormula.fP (P i v) (R.loc v X)) _
      (Finset.mem_univ w)]
end


/-! # SiegelWeilKfpDefs: Consolidated global theta-kernel definitions and proofs (SiegelWeilKfpDefs). -/
@[expose] public section
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula
open GlobalTheory.Doubling (absE)
open Finset (sum_congr prod_congr)
open Matrix (transpose_map transpose_mul transpose_one conjTranspose_mul conjTranspose_one
  conjTranspose_conjTranspose trace_smul)

namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace SD_k
open SD
variable (d : SD_k σ)
abbrev LF : Type := (Fin d.m → Fin d.n → ℂ) → ℂ
abbrev MF : Type := d.MxE → ℂ
def IsAwayW (w : InfinitePlace F) (Ψ : d.MxE → ℂ) : Prop :=
  ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X
def uW (w : InfinitePlace F) (z : ℂ) : AE F E :=
  Krd.sc_k d (Function.update (fun _ => 1) w z) + finOne F • 1
def chiW (w : InfinitePlace F) (z : ℂ) : ℂ :=
  if h : IsUnit (d.uW w z) then ((d.χ h.unit : Circle) : ℂ) else 1
private theorem uW_mul (w : InfinitePlace F) (z z' : ℂ) : d.uW w (z * z') = d.uW w z * d.uW w z' := by
  have hs := (Place.exists_sec d.cm d.B.emb).choose_spec
  have h0 (x) : Krd.sc_k d x * (finOne F • (1 : AE F E)) = 0 := by rw [mul_smul_comm, mul_one, Krd.sc_fin_k]
  have h1 (x) : (finOne F • (1 : AE F E)) * Krd.sc_k d x = 0 := by rw [smul_mul_assoc, one_mul, Krd.sc_fin_k]
  simp only [uW, KC.update_mul, add_mul, mul_add, h0, h1, KC.e_mul_e]; simp only [Krd.sc_k, hs.2.2.2.2]; abel
private theorem uW_one (w : InfinitePlace F) : d.uW w 1 = 1 :=
  Place.ad_ext d.cm d.B.emb
    (fun w' => by rw [uW, map_add (f := _), Krd.sc_pi_k, Place.piInf_finOne, map_one]; simp [Function.update_apply])
    (by rw [uW, smul_add, Krd.sc_fin_k, smul_smul, KC.finOne_mul_self, zero_add])
private theorem uW_isUnit (w : InfinitePlace F) {z : ℂ} (hz : z ≠ 0) : IsUnit (d.uW w z) := by
  have h : d.uW w z * d.uW w z⁻¹ = 1 := by rw [← d.uW_mul, mul_inv_cancel₀ hz, d.uW_one]
  exact ⟨⟨d.uW w z, d.uW w z⁻¹, h, by rw [mul_comm]; exact h⟩, rfl⟩
private theorem uW_cont (w : InfinitePlace F) : Continuous (d.uW w) :=
  ((Krd.sc_cont_k d).comp (continuous_const.update w continuous_id)).add continuous_const
theorem chiW_mul (w : InfinitePlace F) (z z' : ℂ) (hz : z ≠ 0) (hz' : z' ≠ 0) :
    d.chiW w (z * z') = d.chiW w z * d.chiW w z' := by
  have h1 := d.uW_isUnit w hz; have h2 := d.uW_isUnit w hz'; have h3 := d.uW_isUnit w (mul_ne_zero hz hz')
  simp only [chiW, dite_eq_left h3, dite_eq_left h1, dite_eq_left h2]
  rw [show h3.unit = h1.unit * h2.unit from Units.ext (by simp [d.uW_mul]), map_mul, Circle.coe_mul]
theorem chiW_cont (w : InfinitePlace F) : ContinuousOn (d.chiW w) {z : ℂ | z ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  let U : {z : ℂ // z ≠ 0} → (AE F E)ˣ := fun z => (d.uW_isUnit w z.2).unit
  have hU : Continuous U := Units.continuous_iff.2 ⟨(d.uW_cont w).comp continuous_subtypeVal, by
    have e (z : {z : ℂ // z ≠ 0}) : ((U z)⁻¹ : (AE F E)ˣ).1 = d.uW w z.1⁻¹ :=
      Units.inv_eq_of_mul_eq_one_right (by change d.uW w z.1 * d.uW w z.1⁻¹ = 1
                                           rw [← d.uW_mul, mul_inv_cancel₀ z.2, d.uW_one])
    simp only [e]; exact (d.uW_cont w).comp (continuous_subtypeVal.inv₀ fun z => z.2)⟩
  have he : Set.domRestrict {z : ℂ | z ≠ 0} (d.chiW w) = fun z => ((d.χ (U z) : Circle) : ℂ) := funext fun z => by
    rw [Set.domRestrict_apply, chiW, dite_eq_left (d.uW_isUnit w z.2)]
  rw [he]; exact continuous_subtypeVal.comp (d.ok.hecke.1.comp hU)
theorem chiW_pos (w : InfinitePlace F) (r : ℝ) (hr : 0 < r) : d.chiW w (r : ℂ) = 1 := by
  set t := Real.sqrt r
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.mpr hr).ne'
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hc : cA σ (d.uW w t) = d.uW w t := Place.ad_ext d.cm d.B.emb
    (fun w' => by rw [Place.piInf_cA d.cm, uW, map_add (f := _), Krd.sc_pi_k, Place.piInf_finOne, add_zero]
                  by_cases h : w' = w <;> simp [h])
    (by rw [← map_smul, uW, smul_add, Krd.sc_fin_k, zero_add, smul_smul, KC.finOne_mul_self, map_smul, map_one])
  obtain ⟨ξ, hξ⟩ := GlobalTheory.SplitIdele.exists_isQuad d.cm
  let u := (d.uW_isUnit w ht0).unit; let a : (AF F)ˣ := Units.map (Algebra.norm (AF F) : AE F E →* AF F) u
  have ha : Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) a = (d.uW_isUnit w hr0).unit := Units.ext <| by
    show algebraMap (AF F) (AE F E) (Algebra.norm (AF F) (d.uW w t)) = d.uW w (r : ℂ)
    rw [hξ.algebraMap_norm, hc, ← d.uW_mul, ← Complex.ofReal_mul, Real.mul_self_sqrt hr.le]
  have hres := d.ok.res a
  rw [ite_eq_left (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨u, rfl⟩))] at hres
  rw [chiW, dite_eq_left (d.uW_isUnit w hr0), ← ha]; exact hres
theorem om_sch (x : d.G) (Φ : d.Fn) (hΦ : Φ ∈ d.sch) : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ hΦ
theorem T_zero : d.T 0 = 0 := funext fun _ => by
  have h (p : (d.κ → AF F) × (d.κ → AF F)) : schr d.B.ψ p (0 : d.Fn) = 0 := funext fun _ => by simp [schr]
  simp only [SD_k.T, Darboux.rho, h, map_zero, Pi.zero_apply]
theorem T_inj (hT : TAll_k) (Φ : d.Fn) (hΦ : Φ ∈ d.sch) : d.T Φ = 0 → Φ = 0 := (hT.1 F E σ d).2.2 Φ hΦ
end SD_k

def RD_k.GoodAway {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (Ψ : d.MxE → ℂ) : Prop :=
  d.IsAwayW w Ψ ∧ Ψ ≠ 0 ∧ ∀ f, IsSw f → R.tens w f Ψ ∈ d.schM
def GoodAwayEx_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d : SD_k σ) (R : RD_k d) (w : InfinitePlace F), ∃ Ψ, R.GoodAway w Ψ

namespace RD_k
open RD
variable {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F)
theorem cw_gram (X : d.MxE) :
    d.cw w (d.gram X X) = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X)) := by
  rw [KW.cw_gram_k, KW.cw_loc_k R w X, transpose_mul,
    show ((R.fr w).1 * (Matrix.of (R.loc w X)).map star).map star = (R.fr w).1.map star * Matrix.of (R.loc w X) by
      ext _ _; simp [Matrix.mul_apply]]
  calc (Matrix.of (R.loc w X))ᴴ * (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * ((R.fr w).1.map star * Matrix.of (R.loc w X))
      = (Matrix.of (R.loc w X))ᴴ * ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star) *
          Matrix.of (R.loc w X) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [KW.frJ_k, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
theorem frame_diag (y : GR d.n) (A D : d.Mnc) (hy : mR y = Matrix.fromBlocks A 0 0 D) :
    inFrame d.b (R.ι w y) = Matrix.fromBlocks (inFrame d.b (R.ι w y)).toBlocks₁₁ 0 0 (inFrame d.b (R.ι w y)).toBlocks₂₂
      ∧ d.cw w (inFrame d.b (R.ι w y)).toBlocks₁₁ = A ∧ d.cw w (inFrame d.b (R.ι w y)).toBlocks₂₂ = D ∧
    (∀ w', w' ≠ w → d.cw w' (inFrame d.b (R.ι w y)).toBlocks₁₁ = 1 ∧ d.cw w' (inFrame d.b (R.ι w y)).toBlocks₂₂ = 1) ∧
    finOne F • (inFrame d.b (R.ι w y)).toBlocks₁₁ = finOne F • 1 ∧
    finOne F • (inFrame d.b (R.ι w y)).toBlocks₂₂ = finOne F • 1 := by
  set M := inFrame d.b (R.ι w y)
  have hw : d.cw w M = Matrix.fromBlocks A 0 0 D := by rw [R.cw_iota_pf w y, hy, dZ_conj_diag (Krd.zeta_ne R.hζ)]
  have ho := R.off_w w (y := y)
  have o1 := one_blocks (n := d.n) (1 : ℂ); simp only [one_smul] at o1
  have of := one_blocks (n := d.n) (finOne F • (1 : AE F E))
  have hf' : finOne F • M = (finOne F • (1 : AE F E)) • (1 : d.Mn2) := by rw [R.off_f w y, smul_one_smul]
  have z0 (w') : d.cw w' (0 : d.Mn) = 0 := Matrix.map_zero _ (map_zero _)
  have e12 : M.toBlocks₁₂ = 0 := Place.cw_ext_k d
    (fun w' => by rw [z0]; show (d.cw w' M).toBlocks₁₂ = 0; by_cases h : w' = w
                  · rw [h, hw, Matrix.toBlocks_fromBlocks₁₂]
                  · rw [ho w' h]; exact o1.2.1)
    (by show (finOne F • M).toBlocks₁₂ = _; rw [hf', of.2.1, smul_zero])
  have e21 : M.toBlocks₂₁ = 0 := Place.cw_ext_k d
    (fun w' => by rw [z0]; show (d.cw w' M).toBlocks₂₁ = 0; by_cases h : w' = w
                  · rw [h, hw, Matrix.toBlocks_fromBlocks₂₁]
                  · rw [ho w' h]; exact o1.2.2.1)
    (by show (finOne F • M).toBlocks₂₁ = _; rw [hf', of.2.2.1, smul_zero])
  refine ⟨by conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]; rw [e12, e21],
    by show (d.cw w M).toBlocks₁₁ = _; rw [hw, Matrix.toBlocks_fromBlocks₁₁],
    by show (d.cw w M).toBlocks₂₂ = _; rw [hw, Matrix.toBlocks_fromBlocks₂₂],
    fun w' h => ⟨by show (d.cw w' M).toBlocks₁₁ = _; rw [ho w' h]; exact o1.1,
                 by show (d.cw w' M).toBlocks₂₂ = _; rw [ho w' h]; exact o1.2.2.2⟩,
    by show (finOne F • M).toBlocks₁₁ = _; rw [hf', of.1, smul_one_smul],
    by show (finOne F • M).toBlocks₂₂ = _; rw [hf', of.2.2.2, smul_one_smul]⟩
private theorem compFin_det (t : d.Gn) (hf : finOne F • t.1 = finOne F • 1) (v : Pl F) :
    compFin F E v t.1.det = 1 := by
  have hm : t.1.map (compFin F E v) = 1 := Matrix.ext fun i j => by
    rw [Matrix.map_apply, ← Place.compFin_finOne v (t.1 i j)]
    change compFin F E v ((finOne F • t.1) i j) = _
    rw [hf, Matrix.smul_apply, Place.compFin_finOne, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hm, Matrix.det_one]
private theorem piInf_det (t : d.Gn) (a : d.Mnc) (ht : d.cw w t.1 = a) (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1)
    (w' : InfinitePlace F) : piInf (d.B.emb w') t.1.det = Function.update (fun _ => (1 : ℂ)) w a.det w' := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  by_cases h : w' = w
  · subst h; rw [Function.update_self]; exact congrArg Matrix.det ht
  · rw [Function.update_of_ne h]; change (d.cw w' t.1).det = 1; rw [ho w' h, Matrix.det_one]
theorem chi_det (t : d.Gn) (a : d.Mnc) (ht : d.cw w t.1 = a) (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1)
    (hf : finOne F • t.1 = finOne F • 1) : (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) = d.chiW w a.det := by
  have e : t.1.det = d.uW w a.det := PositivityTheory.ThKG.Tow.Levi.ad_ext d.cm d.B.emb
    (fun w' => by rw [piInf_det (d := d) w t a ht ho w', SD_k.uW, map_add (f := _), Krd.sc_pi_k,
                      Place.piInf_finOne, add_zero])
    (fun v => by rw [compFin_det (d := d) t hf v, SD_k.uW, map_add (f := _), ← Place.compFin_finOne v, Krd.sc_fin_k,
                     map_zero, zero_add, Place.compFin_finOne, map_one])
  have hu : IsUnit (d.uW w a.det) := e ▸ (Matrix.GeneralLinearGroup.det t).isUnit
  rw [SD_k.chiW, dite_eq_left hu, show hu.unit = Matrix.GeneralLinearGroup.det t from
    Units.ext (by rw [IsUnit.unit_spec, Matrix.GeneralLinearGroup.val_det_apply, e])]
theorem absE_det (t : d.Gn) (a : d.Mnc) (ht : d.cw w t.1 = a) (ho : ∀ w', w' ≠ w → d.cw w' t.1 = 1)
    (hf : finOne F • t.1 = finOne F • 1) : (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) = ‖a.det‖ ^ 2 := by
  rw [GlobalTheory.Doubling.absE_apply]
  have hinf (w') : GlobalTheory.Doubling.absEw F E w' (GlobalTheory.Doubling.unitInf F E w'
      (Matrix.GeneralLinearGroup.det t)) = ‖Function.update (fun _ => (1 : ℂ)) w a.det w'‖₊ ^ 2 := by
    rw [GlobalTheory.Doubling.absEw_eq_sq d.cm (d.B.emb w'), ← piInf_det (d := d) w t a ht ho w',
      ← Matrix.GeneralLinearGroup.val_det_apply]; rfl
  have hfin (v) : GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v
      (Matrix.GeneralLinearGroup.det t)) = 1 := by
    rw [show GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t) = 1 from Units.ext (by
      show compFin F E v ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) = 1
      rw [Matrix.GeneralLinearGroup.val_det_apply, compFin_det (d := d) t hf v]), map_one]
  simp only [hinf, hfin, finprod_one, mul_one]
  rw [Finset.prod_eq_single w (fun w' _ h => by rw [Function.update_of_ne h, nnNorm_one, one_pow])
    (fun h => absurd (Finset.mem_univ w) h), Function.update_self]; push_cast; rfl
end RD_k

namespace KFock
private def tensL_k {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (f : d.LF) : d.MF →ₗ[ℂ] d.MF where
  toFun := R.tens w f
  map_add' _ _ := funext fun _ => by simp only [RD_k.tens, Pi.add_apply, mul_add]
  map_smul' _ _ := funext fun _ => by simp only [RD_k.tens, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
theorem loc_add_of_k {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (X Z : d.MxE) (h : d.cw w Z = 0) :
    R.loc w (X + Z) = R.loc w X := by
  unfold RD_k.loc
  rw [show d.cw w (X + Z) = d.cw w X + d.cw w Z from Matrix.map_add _ (map_add _) X Z, h, add_zero]
theorem crd_add_k (d : SD_k σ) (X Z : d.MxE) (k : d.I3) : d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  unfold SD_k.crd; rw [Matrix.add_apply, map_add (f := _), Finsupp.add_apply]
theorem crd_fin_k (d : SD_k σ) (Z : d.MxE) (h : finOne F • Z = 0) (k : d.I3) : (d.crd Z k).2 = 0 := by
  have e1 : d.crd (finOne F • Z) k = finOne F * d.crd Z k := by
    unfold SD_k.crd; rw [Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e2 : d.crd (finOne F • Z) k = 0 := by
    rw [h]; unfold SD_k.crd; rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
  have e3 : (finOne F * d.crd Z k).2 = (d.crd Z k).2 := by
    show (finOne F).2 * (d.crd Z k).2 = _; rw [show (finOne F).2 = 1 from rfl, one_mul]
  rw [← e3, ← e1, e2]; rfl
theorem away_inv_k {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) (Ψ : d.MF) (hΨ : Ψ ∈ R.away w) :
    d.IsAwayW w Ψ := fun X Z hZ hf => by
  induction hΨ using Submodule.span_induction generalizing X with
  | mem x hx =>
    obtain ⟨P, g, -, rfl⟩ := hx
    have e2 : (fun k => (d.crd (X + Z) k).2) = fun k => (d.crd X k).2 := funext fun k => by
      rw [crd_add_k]; show (d.crd X k).2 + (d.crd Z k).2 = _; rw [crd_fin_k d Z hf k, add_zero]
    show (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' (X + Z))) * g (fun k => (d.crd (X + Z) k).2) =
      (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g (fun k => (d.crd X k).2)
    rw [prod_congr rfl fun w' hw' => by rw [loc_add_of_k R w' X Z (hZ w' (Finset.ne_of_mem_erase hw'))], e2]
  | zero => rfl
  | add _ _ _ _ hx hy => simp only [Pi.add_apply, hx, hy]
  | smul _ _ _ hx => simp only [Pi.smul_apply, hx]
theorem T_add_k (d : SD_k σ) (Φ Φ' : d.Fn) : d.T (Φ + Φ') = d.T Φ + d.T Φ' := funext fun _ =>
  (congrArg d.l (funext fun _ => mul_add _ _ _)).trans (d.l.map_add _ _)
theorem T_smul_k (d : SD_k σ) (a : ℂ) (Φ : d.Fn) : d.T (a • Φ) = a • d.T Φ := funext fun _ =>
  (congrArg d.l (funext fun _ => mul_left_comm _ _ _)).trans (d.l.map_smul a _)
theorem T_sub_k (d : SD_k σ) (Φ Φ' : d.Fn) : d.T (Φ - Φ') = d.T Φ - d.T Φ' :=
  eq_sub_of_add_eq (by have h := T_add_k d (Φ - Φ') Φ'; rw [sub_add_cancel] at h; exact h.symm)
theorem T_inj_k (hB : TBij_k) (d : SD_k σ) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch)
    (e : d.T Φ = d.T Φ') : Φ = Φ' :=
  sub_eq_zero.mp ((hB F E σ d).2.2 _ (d.sch.sub_mem h h') (by rw [T_sub_k, e, sub_self]))
private theorem prodGen_mem_k (d : SD_k σ) (R : RD_k d) (S : InfinitePlace F → 𝓢(Fin d.m → Fin d.n → ℂ, ℂ))
    (g : d.Af3 → ℂ) (hg : g ∈ SB d.Af3) : (fun X => (∏ w, S w (R.loc w X)) * g fun k => (d.crd X k).2) ∈ d.schM := by
  obtain ⟨T, hT⟩ := piProdSch (InfinitePlace F) (Fin d.m → Fin d.n → ℂ) S
  obtain ⟨L, hL⟩ := archEquiv_k d R
  rw [SD_k.schM, Submodule.mem_comap]
  refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L T, g, hg, funext fun c => ?_⟩
  simp only [LinearMap.funLeft_apply, pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp,
    hT, hL, crd_cmb_k]
theorem fock_le_k (d : SD_k σ) (R : RD_k d) : R.fock ≤ d.schM := Submodule.span_le.mpr fun _ ⟨P, g, hg, h⟩ => by
  subst h
  have heq : (fun X => (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) =
      fun X => (∏ w, (isSw_fP (P w)).choose (R.loc w X)) * g fun k => (d.crd X k).2 :=
    funext fun X => congrArg (· * _) (prod_congr rfl fun w _ => congrFun (isSw_fP (P w)).choose_spec.symm (R.loc w X))
  change (fun X => (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) ∈ d.schM
  rw [heq]; exact prodGen_mem_k d R (fun w => (isSw_fP (P w)).choose) g hg
theorem tens_mem_k (d : SD_k σ) (R : RD_k d) (w : InfinitePlace F) (f : d.LF) (hf : IsSw f)
    (Ψ : d.MF) (hΨ : Ψ ∈ R.away w) : R.tens w f Ψ ∈ d.schM := by
  obtain ⟨φ, hφ⟩ := hf
  refine (Submodule.span_le.mpr ?_ : R.away w ≤ d.schM.comap (tensL_k R w f)) hΨ
  rintro _ ⟨P, g, hg, rfl⟩
  have heq : tensL_k R w f (fun X => (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) *
      g fun k => (d.crd X k).2) =
      fun X => (∏ w', (Function.update (fun w' => (isSw_fP (P w')).choose) w φ w') (R.loc w' X)) *
        g fun k => (d.crd X k).2 := funext fun X => by
    show f (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g fun k => (d.crd X k).2) = _
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, hφ, _root_.mul_assoc]
    exact congrArg (f _ * ·) (congrArg (· * _) <| prod_congr rfl fun w' hw' => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw'), (isSw_fP (P w')).choose_spec])
  change tensL_k R w f _ ∈ d.schM
  rw [heq]; exact prodGen_mem_k d R (Function.update (fun w' => (isSw_fP (P w')).choose) w φ) g hg
theorem fockMem_k : FockMem_k := fun _ _ _ _ _ _ _ _ d R =>
  ⟨fock_le_k d R, fun w Ψ hΨ => ⟨fun P => (Submodule.span_le.mpr (by
    rintro _ ⟨P', g, hg, rfl⟩
    refine Submodule.subset_span ⟨Function.update P' w P, g, hg, funext fun X => ?_⟩
    show fP P (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P' w') (R.loc w' X)) * g fun k => (d.crd X k).2) =
      (∏ w', fP (Function.update P' w P w') (R.loc w' X)) * g fun k => (d.crd X k).2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, _root_.mul_assoc]
    exact congrArg (fP P _ * ·) (congrArg (· * _) <| prod_congr rfl fun w' hw' => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')])) : R.away w ≤ R.fock.comap (tensL_k R w (fP P))) hΨ,
    away_inv_k R w Ψ hΨ⟩,
   fun _ _ hf => _root_.UpperTheory.Reformulated.B.Glb2.fock_dec_k R _ _ hf⟩
theorem liftEx_k (hB : TBij_k) : LiftEx_k := fun F E _ _ _ _ _ σ d R w Ψ hΨ => by
  let t : PX d.m d.n →ₗ[ℂ] d.MF :=
    ⟨⟨fun P => R.tens w (fP P) Ψ, fun _ _ => funext fun _ => by simp only [RD_k.tens, fP_add, Pi.add_apply, add_mul]⟩,
      fun _ _ => funext fun _ => by
        simp only [RD_k.tens, fP_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, _root_.mul_assoc]⟩
  choose φ0 hφ0 using fun P => (hB F E σ d).2.1 (t P) ((fockMem_k F E σ d R).1 (((fockMem_k F E σ d R).2.1 w Ψ hΨ).1 P))
  refine ⟨⟨⟨φ0, fun u v => T_inj_k hB d (hφ0 (u + v)).1 (d.sch.add_mem (hφ0 u).1 (hφ0 v).1)
    (by rw [T_add_k, (hφ0 _).2, (hφ0 _).2, (hφ0 _).2, map_add (f := _)])⟩,
    fun a v => T_inj_k hB d (hφ0 (a • v)).1 (d.sch.smul_mem a (hφ0 v).1)
      (by rw [RingHom.id_apply, T_smul_k, (hφ0 _).2, (hφ0 _).2, map_smul])⟩, hφ0⟩
theorem liftSw1_k (hB : TBij_k) (d : SD_k σ) (R : RD_k d) (w : InfinitePlace F) (f : d.LF)
    (hf : IsSw f) (Ψ : d.MF) (hΨ : Ψ ∈ R.away w) : ∃ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ :=
  (hB F E σ d).2.1 _ (tens_mem_k d R w f hf Ψ hΨ)
theorem goodAway0_k {d : SD_k σ} (R : RD_k d) (w : InfinitePlace F) : ∃ Ψ, R.GoodAway w Ψ ∧ Ψ 0 ≠ 0 := by
  let g := (GlobalTheory.RealLift.intPts F d.I3).indicator (1 : d.Af3 → ℂ)
  let Ψ : d.MF := fun X => (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g fun k => (d.crd X k).2
  have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, GlobalTheory.RealLift.indicator_intPts_mem_SB, rfl⟩
  have h0 : Ψ 0 ≠ 0 := by
    have hg0 : g (fun k => (d.crd (0 : d.MxE) k).2) = 1 := by
      rw [show (fun k => (d.crd (0 : d.MxE) k).2) = 0 from funext fun k => by
        unfold SD_k.crd; rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]; rfl]
      exact Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts _
    exact fun h => (Finset.prod_ne_zero_iff.mpr fun _ _ => fP_one_ne _) (by simpa [Ψ, hg0] using h)
  exact ⟨Ψ, ⟨away_inv_k R w Ψ hΨ, fun hz => h0 (by rw [hz]; rfl), fun f hf => tens_mem_k d R w f hf Ψ hΨ⟩, h0⟩
theorem goodAwayEx_k : GoodAwayEx_k := fun _ _ _ _ _ _ _ _ _ R w =>
  let ⟨Ψ, h, _⟩ := goodAway0_k R w; ⟨Ψ, h⟩
end KFock

namespace Krd.DM
open Krd.DC
variable (d : SD_k σ)
theorem inFrame_mul_k (x z : d.G) : inFrame d.b (x * z) = inFrame d.b x * inFrame d.b z := d.inFrame_mul x z
theorem inFrame_inj_k {x z : d.G} (h : inFrame d.b x = inFrame d.b z) : x = z := d.inFrame_inj h
end Krd.DM

open Krd Krd.DM Krd.DC in
theorem Krd.denseW_k : DenseW_k := by
  intro F E _ _ _ _ _ σ d R w y O hO hy
  have h0 := zeta_ne R.hζ
  have hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n R.ε := R.hε
  obtain ⟨X, hXU, hXO⟩ := exists_rat d.cm (d.B.emb w).1 R.hζ hO hy
  have hX := rat_unitary d.cm (d.B.emb w).1 R.ε X hXU
  have hdetJ : (dbl d.Y.J).det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hε; rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul] at this
    exact QR_det_ne E R.ε this.symm
  set bX := d.b.1 * X * (d.b⁻¹).1
  have hbXu : bXᵀ * dbl d.Y.J * bX.map σ = dbl d.Y.J :=
    conj_unitE (σ : E →+* E) d.b.1 (d.b⁻¹).1 X (dbl d.Y.J) (QR E d.n R.ε) (Units.mul_inv d.b) hε hX
  let gX : d.G := ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F))
    (Matrix.nonsingInvUnit bX (isUnit_iff_ne_zero.2 (det_ne_of (σ : E →+* E) hbXu hdetJ))), by
      show (incM F bX)ᵀ * dbl (incM F d.Y.J) * (incM F bX).map (cA σ) = dbl (incM F d.Y.J)
      rw [dbl_incM_k d, incM_cA, incM_alt_bis, ← _root_.PositivityTheory.SiegelWeilFormula.KK.incM_mul', ← _root_.PositivityTheory.SiegelWeilFormula.KK.incM_mul', hbXu]⟩
  have hfgX : inFrame d.b gX = incM F X := by
    show incM F (d.b⁻¹).1 * incM F bX * incM F d.b.1 = incM F X; rw [← _root_.PositivityTheory.SiegelWeilFormula.KK.incM_mul', ← _root_.PositivityTheory.SiegelWeilFormula.KK.incM_mul']; congr 1
    simp only [bX, ← mul_assoc, Units.inv_mul, one_mul]; rw [mul_assoc, Units.inv_mul, mul_one]
  refine ⟨gX, Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩, _, hXO, gX * (R.ι w (Phi R.hζ ⟨_, hXU⟩))⁻¹,
    (inv_mul_cancel_right _ _).symm, fun y'' => ?_⟩
  set y' := Phi R.hζ ⟨X.map (d.B.emb w).1, hXU⟩; set A := inFrame d.b (gX * (R.ι w y')⁻¹) with hA
  have hAC : A * inFrame d.b (R.ι w y') = incM F X := by rw [hA, ← inFrame_mul_k, inv_mul_cancel_right, hfgX]
  have hC : d.cw w (inFrame d.b (R.ι w y')) = X.map (d.B.emb w).1 := by
    have e := R.at_w w y'
    rw [show mR y' = dZ d.n R.ζ * X.map (d.B.emb w).1 * dZ d.n R.ζ⁻¹ from rfl, mul_assoc _ (dZ _ R.ζ⁻¹),
      dZ_inv_mul h0, mul_one] at e
    simpa only [← mul_assoc, dZ_inv_mul h0, one_mul] using congrArg (fun M => dZ d.n R.ζ⁻¹ * M) e
  have hdet := det_of_inU hXU
  have hAw : d.cw w A = 1 := by
    have e : d.cw w A * X.map (d.B.emb w).1 = X.map (d.B.emb w).1 := by
      have := congrArg (d.cw w) hAC; rwa [cw_mul_k, hC, cw_incM_k] at this
    calc d.cw w A = d.cw w A * X.map (d.B.emb w).1 * (X.map (d.B.emb w).1)⁻¹ := by
          rw [mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
      _ = 1 := by rw [e, Matrix.mul_nonsing_inv _ hdet]
  apply inFrame_inj_k d; rw [inFrame_mul_k d _ (R.ι w y''), inFrame_mul_k d (R.ι w y''), ← hA]
  refine Place.cw_ext_k d (fun w' => ?_)
    (by rw [fin_mul, fin_mul, R.off_f w y'', ← fin_mul, ← fin_mul, mul_one, one_mul])
  rw [cw_mul_k, cw_mul_k]
  by_cases hw : w' = w
  · subst hw; rw [hAw, one_mul, mul_one]
  · rw [R.off_w w w' y'' hw, one_mul, mul_one]

namespace KSplitW
variable (d : SD_k σ)
theorem cw_iota_k (R : RD_k d) (w : InfinitePlace F) (y : GR d.n) :
    d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := R.cw_iota_pf w y
theorem decompW_k (R : RD_k d) (w : InfinitePlace F) (g : d.G) :
    ∃ (x : d.G) (y : GR d.n), g = x * R.ι w y ∧ d.cw w (inFrame d.b x) = 1 := by
  have h0 := Krd.zeta_ne R.hζ; set Zw := d.cw w (inFrame d.b g)
  let y : GR d.n := Krd.DM.mkG (dZ d.n R.ζ * Zw * dZ d.n R.ζ⁻¹)
    (Krd.inG_conj R.hζ Zw (KSing.UnitaryGroupBasics.form_w_k d R w g))
  refine ⟨g * (R.ι w y)⁻¹, y, by rw [inv_mul_cancel_right], ?_⟩
  have hy : d.cw w (inFrame d.b (R.ι w y)) = Zw := by
    rw [cw_iota_k, Krd.DM.mR_mkG]; simp only [← mul_assoc, Krd.dZ_inv_mul h0, one_mul]
    rw [mul_assoc, Krd.dZ_inv_mul h0, mul_one]
  have hinv : Zw * d.cw w (inFrame d.b g⁻¹) = 1 := by
    rw [← Krd.cw_mul_k, ← d.inFrame_mul, mul_inv_cancel, d.inFrame_one, Krd.cw_one_k]
  have e : d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * Zw = Zw := by
    conv_lhs => rw [← hy]
    rw [← Krd.cw_mul_k, ← d.inFrame_mul, inv_mul_cancel_right]
  calc d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) = d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) *
        (Zw * d.cw w (inFrame d.b g⁻¹)) := by rw [hinv, mul_one]
    _ = 1 := by rw [← mul_assoc, e, hinv]
theorem commW_k (R : RD_k d) (w : InfinitePlace F) (x : d.G) (hx : d.cw w (inFrame d.b x) = 1) (y : GR d.n) :
    x * R.ι w y = R.ι w y * x := by
  apply d.inFrame_inj; rw [d.inFrame_mul, d.inFrame_mul]
  refine Place.cw_ext_k d (fun w' => ?_) (by
    rw [Krd.fin_mul, Krd.fin_mul, R.off_f]
    simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul])
  rw [Krd.cw_mul_k, Krd.cw_mul_k]
  by_cases h : w' = w
  · subst h; rw [hx, one_mul, mul_one]
  · rw [R.off_w w w' y h, one_mul, mul_one]
theorem finOne_one_mem_k (i j : d.N2) : finOne F • (1 : d.Mn2) i j ∈ intHat F E := by
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq]; exact finOne_mem
  · rw [Matrix.one_apply_ne h, smul_zero]; exact zero_mem _
theorem iota_mem_K_k (R : RD_k d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y)) : R.ι w y ∈ d.K := by
  have h0 := Krd.zeta_ne R.hζ; rw [d.ok.stdK]
  refine ⟨fun w' => ?_, fun k' hk' i j => ?_⟩
  · change d.cw w' (inFrame d.b (R.ι w y)) * (d.cw w' (inFrame d.b (R.ι w y)))ᴴ = 1
    by_cases h : w' = w
    · subst h
      have hD : dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_mul_inv h0]
      rw [cw_iota_k, dZ_inv_ct R.hζ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
      calc (dZ d.n R.ζ)ᴴ * mR y * dZ d.n R.ζ * ((dZ d.n R.ζ)ᴴ * ((mR y)ᴴ * dZ d.n R.ζ))
          = (dZ d.n R.ζ)ᴴ * (mR y * (dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ) * (mR y)ᴴ) * dZ d.n R.ζ := by simp only [mul_assoc]
        _ = 1 := by rw [hD, mul_one, mul_eq_one_comm.1 hy.2, mul_one, ← dZ_inv_ct R.hζ, Krd.dZ_inv_mul h0]
    · rw [R.off_w w w' y h, conjTranspose_one, mul_one]
  · obtain ⟨z, rfl⟩ : ∃ z, k' = R.ι w z := by
      rcases hk' with rfl | hk'; · exact ⟨y, rfl⟩
      rw [Set.mem_singleton_iff] at hk'; exact ⟨y⁻¹, by rw [hk', map_inv]⟩
    have e := congrFun (congrFun (R.off_f w z) i) j; rw [Matrix.smul_apply, Matrix.smul_apply] at e
    rw [e]; exact finOne_one_mem_k d i j
theorem kSplit_k (R : RD_k d) (w : InfinitePlace F) (k : d.G) (hk : k ∈ d.K) :
    ∃ y : GR d.n, (R.ι w y)⁻¹ * k ∈ d.K ∧ d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by
  have h0 := Krd.zeta_ne R.hζ; obtain ⟨x, y, hxy, hx⟩ := decompW_k d R w k
  have hkx : (R.ι w y)⁻¹ * k = x := by rw [hxy, commW_k d R w x hx y, inv_mul_cancel_left]
  have hD : dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_mul_inv h0]
  have hD' : (dZ d.n R.ζ)ᴴ * dZ d.n R.ζ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_inv_mul h0]
  have hkw : d.cw w (inFrame d.b k) = (dZ d.n R.ζ)ᴴ * mR y * dZ d.n R.ζ := by
    rw [hxy, d.inFrame_mul, Krd.cw_mul_k, hx, one_mul, cw_iota_k, dZ_inv_ct R.hζ]
  have hM : mR y = dZ d.n R.ζ * d.cw w (inFrame d.b k) * (dZ d.n R.ζ)ᴴ := by
    rw [hkw]; simp only [← mul_assoc]; rw [hD, one_mul, mul_assoc, hD, mul_one]
  have hK : InK (mR y) := ⟨y.2, by
    rw [hM, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    calc dZ d.n R.ζ * ((d.cw w (inFrame d.b k))ᴴ * (dZ d.n R.ζ)ᴴ) *
          (dZ d.n R.ζ * d.cw w (inFrame d.b k) * (dZ d.n R.ζ)ᴴ)
        = dZ d.n R.ζ * ((d.cw w (inFrame d.b k))ᴴ * ((dZ d.n R.ζ)ᴴ * dZ d.n R.ζ) * d.cw w (inFrame d.b k)) *
          (dZ d.n R.ζ)ᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by
          have hk1 : d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1 := ((d.ok.stdK k).1 hk).1 w
          rw [hD', Matrix.mul_one, mul_eq_one_comm.1 hk1, Matrix.mul_one, hD]⟩
  exact ⟨y, (d.K).mul_mem ((d.K).inv_mem (iota_mem_K_k d R w y hK)) hk, hkx ▸ hx⟩
end KSplitW

namespace KFP
variable {d : SD_k σ}
abbrev M1 (d : SD_k σ) := d.MxE
abbrev M2 (d : SD_k σ) (K : Type) := Matrix d.N2 d.N2 K
abbrev Yf_k (d : SD_k σ) : Type := d.Af3
abbrev Iw_k (d : SD_k σ) : Type := InfinitePlace F × Fin d.m × Fin d.n × Bool
abbrev Vw_k (d : SD_k σ) : Type := EuclideanSpace ℝ (Iw_k d)
def fin_k (d : SD_k σ) (X : M1 d) : Yf_k d := fun k => (d.crd X k).2
def arc_k (R : RD_k d) (X : M1 d) : Vw_k d :=
  (EuclideanSpace.equiv (Iw_k d) ℝ).symm fun i =>
    if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im
def gau_k (R : RD_k d) (X : M1 d) : ℂ := ∏ w, fP (1 : PX d.m d.n) (R.loc w X)
def vac_k (R : RD_k d) (g : Yf_k d → ℂ) (X : M1 d) : ℂ := gau_k R X * g (fin_k d X)
theorem vac_mem_k (R : RD_k d) {g : Yf_k d → ℂ} (hg : g ∈ SB (Yf_k d)) : vac_k R g ∈ R.fock :=
  Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
theorem exists_lift_k (hT : TAll_k) (hF : FockMem_k) (R : RD_k d) {g : Yf_k d → ℂ} (hg : g ∈ SB (Yf_k d)) :
    ∃ Ω ∈ d.sch, d.T Ω = vac_k R g := (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 (vac_mem_k R hg))
def zOf_k (u : Iw_k d → ℝ) : InfinitePlace F → Fin d.m → Fin d.n → ℂ :=
  fun w a j => ⟨u (w, a, j, true), u (w, a, j, false)⟩
theorem arc_eq_iff_k (R : RD_k d) (X : M1 d) (u : Vw_k d) :
    arc_k R X = u ↔ ∀ w, R.loc w X = zOf_k (EuclideanSpace.equiv (Iw_k d) ℝ u) w := by
  refine ⟨by rintro rfl w; funext a j; apply Complex.ext <;> simp [zOf_k, arc_k], fun h => ?_⟩
  apply (EuclideanSpace.equiv (Iw_k d) ℝ).injective; funext ⟨w, a, j, b⟩
  have hw := congrFun (congrFun (h w) a) j
  cases b <;> simp only [arc_k, ContinuousLinearEquiv.apply_symm_apply, Bool.false_eq_true, ite_false, ite_true] <;>
    rw [hw] <;> rfl
theorem exists_jn_k (R : RD_k d) (u : Vw_k d) (y : Yf_k d) : ∃! X : M1 d, arc_k R X = u ∧ fin_k d X = y := by
  obtain ⟨L, hL⟩ := KFock.archEquiv_k d R; set Z := zOf_k (EuclideanSpace.equiv (Iw_k d) ℝ u); let cI := L.symm Z
  let c : d.I3 → AF F := fun k => (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (cI k)) (y k) : AF F)
  have hc1 : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) = cI :=
    funext fun _ => RingEquiv.apply_symm_apply _ _
  refine ⟨d.cmb c, ⟨(arc_eq_iff_k R _ _).2 fun w => by
    rw [← hL c w, hc1]; exact congrFun (ContinuousLinearEquiv.apply_symm_apply L Z) w,
    funext fun k => by show (d.crd (d.cmb c) k).2 = y k; rw [KFock.crd_cmb_k]⟩, ?_⟩
  rintro X ⟨hX1, hX2⟩; rw [arc_eq_iff_k] at hX1
  have e2 : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) = cI := by
    have h := congrArg L.symm (funext fun w => by rw [hL, KFock.cmb_crd_k]; exact hX1 w : L _ = Z)
    rwa [ContinuousLinearEquiv.symm_apply_apply] at h
  have e3 : d.crd X = c := funext fun k => Prod.ext
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).injective <| by rw [congrFun e2 k]; exact (congrFun hc1 k).symm)
    (congrFun hX2 k)
  rw [← e3, KFock.cmb_crd_k]
def jn_k (R : RD_k d) (u : Vw_k d) (y : Yf_k d) : M1 d := (exists_jn_k R u y).exists.choose
theorem arc_jn_k (R : RD_k d) (u : Vw_k d) (y : Yf_k d) : arc_k R (jn_k R u y) = u :=
  (exists_jn_k R u y).exists.choose_spec.1
theorem fin_jn_k (R : RD_k d) (u : Vw_k d) (y : Yf_k d) : fin_k d (jn_k R u y) = y :=
  (exists_jn_k R u y).exists.choose_spec.2
theorem jn_arc_fin_k (R : RD_k d) (X : M1 d) : jn_k R (arc_k R X) (fin_k d X) = X :=
  (exists_jn_k R (arc_k R X) (fin_k d X)).unique (exists_jn_k R (arc_k R X) (fin_k d X)).exists.choose_spec ⟨rfl, rfl⟩
def hg_k (R : RD_k d) (νf : Measure (Yf_k d)) (f : M1 d → ℂ) (g : Yf_k d → ℂ) (u : Vw_k d) : ℂ :=
  ∫ y, f (jn_k R u y) * star (g y) ∂νf
def B_k (ν : Measure (M1 d)) (Φ Ψ : d.Fn) : ℂ := ∫ X, d.T Φ X * star (d.T Ψ X) ∂ν
abbrev spf_k (d : SD_k σ) (a b : d.M2) : AF F := symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) a b
def rot_k (R : RD_k d) (t : ℝ) : d.G :=
  (((Finset.univ : Finset (InfinitePlace F)).toList).map fun w => R.ι w (yrot d.n (R.sg w) t)).prod
theorem rot_mem_k (R : RD_k d) (t : ℝ) : rot_k R t ∈ d.K :=
  d.K.list_prod_mem fun _ hx => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact KSplitW.iota_mem_K_k d R w _ (by rw [mR_yrot]; exact inK_yrotM _ _ _)
theorem exists_tw_k (R : RD_k d) (W : M1 d) :
    ∃ W' : M1 d, finOne F • W' = 0 ∧ ∀ w, d.cw w W' = (-(((R.sg w : ℤ) : ℂ) * R.ζ)) • d.cw w W :=
  ⟨Krd.sc_k d (fun w => -(((R.sg w : ℤ) : ℂ) * R.ζ)) • W,
    Matrix.ext fun _ _ => by simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
                             rw [← smul_mul_assoc, Krd.sc_fin_k, zero_mul],
    fun w => Matrix.ext fun _ _ => by
      simp only [SD_k.cw, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, _root_.map_mul, Krd.sc_pi_k]⟩
def tw_k (R : RD_k d) (W : M1 d) : M1 d := (exists_tw_k R W).choose
def vline_k (R : RD_k d) (W : M1 d) (z : ℂ) : d.M2 :=
  (realAd F z.re • W) * (incM F d.b.1.toCols₂)ᵀ + (realAd F z.im • tw_k R W) * (incM F d.b.1.toCols₁)ᵀ
theorem fin_eq_zero_iff_k (X : M1 d) : fin_k d X = 0 ↔ finOne F • X = 0 := by
  set bas := Algebra.TensorProduct.basis (AF F) d.bs
  have key (z : AE F E) : finOne F • z = 0 ↔ ∀ l, (bas.repr z l).2 = 0 := by
    rw [← bas.repr.injective.eq_iff, LinearEquiv.map_smul, LinearEquiv.map_zero]
    simp only [Finsupp.ext_iff, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply,
      finOne_mul_eq_zero_iff]
  exact ⟨fun h => Matrix.ext fun i j => (key _).2 fun l => congrFun h (i, j, l),
    fun h => funext fun ⟨i, j, l⟩ => (key (X i j)).1 (by simpa using congrFun (congrFun h i) j) l⟩
private theorem rho_smul_k (w : d.M2) (c : ℂ) (φ : d.Fn) : d.dd.rho d.B.ψ w (c • φ) = c • d.dd.rho d.B.ψ w φ :=
  funext fun _ => mul_left_comm _ _ _
theorem T_rho_sum'_k (hH : THeis_k) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (Z Z' X : M1 d) :
    d.T (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₂)ᵀ + Z' * (incM F d.b.1.toCols₁)ᵀ) Φ) X =
      d.B.ψ (-(⅟(2 : AF F) * spf_k d (Z * (incM F d.b.1.toCols₂)ᵀ) (Z' * (incM F d.b.1.toCols₁)ᵀ))) *
        (d.B.ψ (d.tt (d.gram Z' (X + Z))) * d.T Φ (X + Z)) := by
  set a := Z * (incM F d.b.1.toCols₂)ᵀ; set b := Z' * (incM F d.b.1.toCols₁)ᵀ
  have h2 : d.dd.rho d.B.ψ (a + b) Φ =
      d.B.ψ (-(⅟(2 : AF F) * spf_k d a b)) • d.dd.rho d.B.ψ a (d.dd.rho d.B.ψ b Φ) := by
    have h3 := congrArg (fun x : d.Fn => d.B.ψ (-(⅟(2 : AF F) * spf_k d a b)) • x)
      (Tpar.rho_rho (dd := d.dd) (ψ := d.B.ψ) a b Φ)
    change d.B.ψ (-(⅟(2 : AF F) * spf_k d a b)) • d.dd.rho d.B.ψ a (d.dd.rho d.B.ψ b Φ) =
      d.B.ψ (-(⅟(2 : AF F) * spf_k d a b)) • (d.B.ψ (⅟(2 : AF F) * spf_k d a b) • d.dd.rho d.B.ψ (a + b) Φ) at h3
    rw [smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul] at h3; exact h3.symm
  have hrb : d.dd.rho d.B.ψ b Φ ∈ d.sch := GlobalTheory.SchrKeepsSchA.schr_mem_schA F d.B.ψ d.ok.good.std d.κ _ Φ hΦ
  rw [h2, KFock.T_smul_k, Pi.smul_apply, smul_eq_mul, (hH F E σ d _ hrb Z X).1, (hH F E σ d Φ hΦ Z' (X + Z)).2]
theorem B_rel'_k (hT : TAll_k) (hU : TUnit_k) {ν : Measure (M1 d)} (hν : ν.IsAddHaarMeasure) {k : d.G} {χ : ℂ}
    (hχ : χ ≠ 0) {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hk : d.om k Ω = χ • Ω) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (q : Polynomial ℂ)
    (hq : ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0) (v : d.M2) :
    ∑ i ∈ Finset.range (q.natDegree + 1),
      q.coeff i * (star χ)⁻¹ ^ i * B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = 0 := by
  have hS := d.ok.dbl.weil.2.1.toIsSplitting
  have hrho (w) (φ) (hφ : φ ∈ d.sch) : d.dd.rho d.B.ψ w φ ∈ d.sch :=
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F d.B.ψ d.ok.good.std d.κ _ φ hφ
  have hpow (i : ℕ) : d.om (k ^ i) Ω = χ ^ i • Ω := by
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, _root_.map_mul, mul_apply_eq_comp, hk, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hact (i : ℕ) : actB (cA σ) (k ^ i) (actB (cA σ) (k⁻¹ ^ i) v) = v := by
    have e1 : k ^ i * k⁻¹ ^ i = 1 := by rw [inv_pow, mul_inv_cancel]
    simp only [actB]; rw [Matrix.mul_assoc, ← transpose_mul, ← Units.val_mul, ← Subgroup.coe_mul, e1]
    simp only [OneMemClass.coe_one, Units.val_one, transpose_one, Matrix.mul_one]
  set Ψ := d.dd.rho d.B.ψ v Ω; have hΨ : Ψ ∈ d.sch := hrho v Ω hΩ
  have hterm (i : ℕ) : (star χ)⁻¹ ^ i * B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) =
      B_k ν (d.om (k ^ i) Φ) Ψ := by
    have h1 := hU F E σ d ν hν (k ^ i) Φ hΦ _ (hrho (actB (cA σ) (k⁻¹ ^ i) v) Ω hΩ)
    rw [show d.om (k ^ i) (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω) = χ ^ i • Ψ by
      rw [hS.impl _ _ Ω hΩ, hact, hpow, rho_smul_k], KFock.T_smul_k] at h1
    unfold B_k; rw [← h1]
    simp_rw [show ∀ X, d.T (d.om (k ^ i) Φ) X * star ((χ ^ i • d.T Ψ) X) =
      star χ ^ i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) from fun _ => by
        rw [Pi.smul_apply, smul_eq_mul, star_mul', star_pow]; ring]
    rw [integral_const_mul, ← _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ (star_ne_zero.2 hχ), _root_.one_pow,
      _root_.one_mul]
  have hlp {f : M1 d → ℂ} (hf : f ∈ d.schM) : MemLp f 2 ν := by
    obtain ⟨_, _, _, _⟩ := KFock.mxTop_k d
    have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
    have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
    have : BorelSpace (AF F) := ⟨rfl⟩; have : BorelSpace (d.I3 → AF F) := Pi.borelSpace
    let e : (d.I3 → AF F) ≃ᵐ M1 d := (KFock.cmbE_k d).toHomeomorph.toMeasurableEquiv
    have : (Measure.map e.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν (KFock.cmbE_k d).symm
    have h1 : MemLp (f ∘ e) 2 (Measure.map e.symm ν) :=
      memLpSchA _ BorelSpace.measurable_eq _ inferInstance (Submodule.mem_comap.mp hf)
    have h2 := e.memLp_map_measure_iff.2 h1
    rwa [MeasurableEquiv.map_map_symm] at h2
  have hint (i : ℕ) : Integrable (fun X => d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ν :=
    (hlp ((hT.1 F E σ d).1 _ (hS.pres (k ^ i) Φ hΦ))).integrable_mul (hlp ((hT.1 F E σ d).1 Ψ hΨ)).star
  let TL : d.Fn →ₗ[ℂ] d.MF := ⟨⟨d.T, KFock.T_add_k d⟩, KFock.T_smul_k d⟩
  calc ∑ i ∈ Finset.range (q.natDegree + 1),
        q.coeff i * (star χ)⁻¹ ^ i * B_k ν Φ (d.dd.rho d.B.ψ (actB (cA σ) (k⁻¹ ^ i) v) Ω)
      = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * B_k ν (d.om (k ^ i) Φ) Ψ :=
        sum_congr rfl fun i _ => by rw [_root_.mul_assoc, hterm]
    _ = ∫ X, ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * (d.T (d.om (k ^ i) Φ) X * star (d.T Ψ X)) ∂ν := by
        unfold B_k; rw [integral_finsetSum _ fun i _ => (hint i).const_mul _]; simp_rw [integral_const_mul]
    _ = ∫ X, TL (∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ) X * star (d.T Ψ X) ∂ν := by
        congr 1; funext X; rw [map_sum, Finset.sum_apply, Finset.sum_mul]
        exact sum_congr rfl fun _ _ => by rw [TL.map_smul, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc]; rfl
    _ = 0 := by rw [hq, TL.map_zero]; simp only [Pi.zero_apply, zero_mul, integral_zero]
theorem cw_mul'_k (w : InfinitePlace F) {p q r : Type} [Fintype q] (A : Matrix p q (AE F E)) (B : Matrix q r (AE F E)) :
    d.cw w (A * B) = d.cw w A * d.cw w B := Matrix.map_mul
theorem cw_add'_k (w : InfinitePlace F) {p q : Type} (A B : Matrix p q (AE F E)) :
    d.cw w (A + B) = d.cw w A + d.cw w B := Matrix.map_add _ (map_add _) A B
theorem cw_one'_k (w : InfinitePlace F) : d.cw w (1 : d.Mn2) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
theorem cw_transpose'_k (w : InfinitePlace F) {p q : Type} (A : Matrix p q (AE F E)) : d.cw w Aᵀ = (d.cw w A)ᵀ := rfl
theorem incM_b_inv_mul_k (d : SD_k σ) : incM F ((d.b⁻¹ : GL _ E) : M2 d E) * incM F (d.b : M2 d E) = 1 := Krd.bb'_k d
theorem matrixRep_eq_frameConj (x : d.G) :
    mat2 x = incM F (d.b : M2 d E) * inFrame d.b x * incM F ((d.b⁻¹ : GL _ E) : M2 d E) := by
  simp only [inFrame, mul_assoc]; rw [Krd.bb_k d, mul_one, ← mul_assoc, Krd.bb_k d, one_mul]
theorem dZ_cw_rot'_k (R : RD_k d) (t : ℝ) (w : InfinitePlace F) :
    dZ d.n R.ζ * d.cw w (inFrame d.b (rot_k R t)) = yrotM d.n (R.sg w) t * dZ d.n R.ζ := by
  have hprod : ∀ L : List (InfinitePlace F), L.Nodup →
      d.cw w (inFrame d.b ((L.map fun w' => R.ι w' (yrot d.n (R.sg w') t)).prod)) =
        if w ∈ L then d.cw w (inFrame d.b (R.ι w (yrot d.n (R.sg w) t))) else 1 := fun L => by
    induction L with
    | nil => intro _; simp only [List.map_nil, List.prod_nil, List.not_mem_nil, ↓reduceIte, d.inFrame_one, cw_one'_k]
    | cons a L ih =>
      intro hL; rw [List.nodup_cons] at hL; rw [List.map_cons, List.prod_cons, d.inFrame_mul, cw_mul'_k, ih hL.2]
      by_cases h : w = a
      · subst h; rw [ite_eq_right hL.1, ite_eq_left (List.mem_cons_self ..), Matrix.mul_one]
      · rw [R.off_w a w _ h, Matrix.one_mul]; simp only [List.mem_cons, h, false_or]
  rw [rot_k, hprod _ (Finset.nodup_toList _), ite_eq_left (Finset.mem_toList.2 (Finset.mem_univ w)), R.at_w, mR_yrot]
private theorem cw_realAd (w : InfinitePlace F) {p q : Type} (t : ℝ) (Y : Matrix p q (AE F E)) :
    d.cw w (realAd F t • Y) = (t : ℂ) • d.cw w Y :=
  Matrix.ext fun _ _ => GlobalTheory.RealScalar.piInf_realAd_smul (d.B.emb w) t (Y _ _)
private theorem sg_sq (R : RD_k d) (w : InfinitePlace F) : ((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h]
private theorem re_trace_loc (R : RD_k d) (w : InfinitePlace F) (W X : M1 d) :
    (((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w X)).trace).re =
      ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w X i j).re + (R.loc w W i j).im * (R.loc w X i j).im) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Complex.re_sum]
  rw [Finset.sum_comm]; exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by simp [Complex.mul_re]
private theorem inner_arc (R : RD_k d) (W X : M1 d) :
    ⟪arc_k R W, arc_k R X⟫_ℝ =
      ∑ w, ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w X i j).re + (R.loc w W i j).im * (R.loc w X i j).im) := by
  simp only [arc_k, PiLp.inner_apply, EuclideanSpace.equiv, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun _ _ => ?_; rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun _ _ => ?_; rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun _ _ => ?_; rw [Fintype.sum_bool]; simp; ring
private theorem trace_evI_trace (z : AE F E) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) z)) =
      ∑ w, 2 * (piInf (d.B.emb w) z).re := by
  rw [Dense.trace_evI d.cm.1]
  exact sum_congr rfl fun w _ => by
    rw [Dense.ext_trace d.cm (d.B.emb w), Dense.piInf_cA d.cm, Complex.add_re, Complex.star_def, Complex.conj_re]; ring
theorem psi_tw'_k (R : RD_k d) {W : M1 d} (_ : finOne F • W = 0) (t : ℝ) (X : M1 d) :
    d.B.ψ (d.tt (d.gram (realAd F t • tw_k R W) X)) =
      Complex.exp (4 * Real.pi * Complex.I * t * ⟪arc_k R W, arc_k R X⟫_ℝ) := by
  have htw : finOne F • tw_k R W = 0 ∧ ∀ w, d.cw w (tw_k R W) = (-(((R.sg w : ℤ) : ℂ) * R.ζ)) • d.cw w W :=
    (exists_tw_k R W).choose_spec
  have hfin : finOne F • d.gram (realAd F t • tw_k R W) X = 0 := by
    unfold SD_k.gram
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, smul_comm, htw.1, smul_zero,
      Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul]
  have hf' : finOne F * d.tt (d.gram (realAd F t • tw_k R W) X) = 0 := by
    unfold SD_k.tt
    rw [← smul_eq_mul, ← LinearMap.map_smul, ← trace_smul, hfin, Matrix.trace_zero, map_zero]
  have htt : d.B.ψ (d.tt (d.gram (realAd F t • tw_k R W) X)) =
      Complex.exp (-(2 * Real.pi * Complex.I) *
        ((∑ w, 2 * ((d.cw w (d.gram (realAd F t • tw_k R W) X)).trace).re : ℝ) : ℂ)) := by
    rw [d.std.2.2 _ (Place.at_of_finOne hf')]; unfold SD_k.tt; rw [trace_evI_trace]
    congr 3; exact sum_congr rfl fun w _ => by
      rw [show piInf (d.B.emb w) (d.gram (realAd F t • tw_k R W) X).trace =
        (d.cw w (d.gram (realAd F t • tw_k R W) X)).trace by
        simp only [Matrix.trace, Matrix.diag_apply, SD_k.cw, Matrix.map_apply, map_sum]]
  have hcw (w) : d.cw w (d.gram (realAd F t • tw_k R W) X) =
      (-(t : ℂ)) • ((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w X)) := by
    rw [KW.cw_gram_k, cw_realAd, htw.2, KW.cw_loc_k R w W, KW.cw_loc_k R w X,
      show ((R.fr w).1 * (Matrix.of (R.loc w X)).map star).map star = (R.fr w).1.map star * Matrix.of (R.loc w X) by
        ext _ _; simp [Matrix.mul_apply]]
    have hz := KW.zeta_ne_k R
    simp only [Matrix.transpose_smul, Matrix.smul_mul, transpose_mul]
    calc _ = ((t : ℂ) * (-(((R.sg w : ℤ) : ℂ) * R.ζ))) • (((Matrix.of (R.loc w W)).map star)ᵀ *
          ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star) * Matrix.of (R.loc w X)) := by
          rw [smul_smul]; simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [KW.frJ_k R w, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
          congr 1; field_simp; linear_combination (-(t : ℂ)) * sg_sq R w
  rw [htt, inner_arc]; congr 1
  have e (w) : ((d.cw w (d.gram (realAd F t • tw_k R W) X)).trace).re =
      -t * ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w X i j).re + (R.loc w W i j).im * (R.loc w X i j).im) := by
    rw [hcw, trace_smul, smul_eq_mul, ← re_trace_loc]; simp [Complex.mul_re]
  simp only [e]; push_cast; rw [Finset.mul_sum, Finset.mul_sum]
  simp only [← Finset.mul_sum]; ring_nf
theorem psi_sp'_k (R : RD_k d) {W : M1 d} (hW : finOne F • W = 0) (s t : ℝ) :
    d.B.ψ (-(⅟(2 : AF F) * spf_k d ((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)
      ((realAd F t • tw_k R W) * (incM F d.b.1.toCols₁)ᵀ))) =
      Complex.exp (-(2 * Real.pi * Complex.I * s * t * ‖arc_k R W‖ ^ 2)) := by
  have hx : finOne F • ((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ) = 0 := by
    rw [← Matrix.smul_mul, smul_comm, hW, smul_zero, Matrix.zero_mul]
  set Z := -(((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
    ((realAd F t • tw_k R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace
  have hz : finOne F • Z = 0 := by
    simp only [Z]
    rw [smul_neg, ← trace_smul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, hx,
      Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero, neg_zero]
  have hf' : finOne F * -(⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) Z) = 0 := by
    rw [mul_neg, mul_left_comm, show finOne F * Algebra.trace (AF F) (AE F E) Z = 0 by
      rw [← smul_eq_mul, ← LinearMap.map_smul, hz, map_zero], mul_zero, neg_zero]
  have hsp : spf_k d ((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ) ((realAd F t • tw_k R W) * (incM F d.b.1.toCols₁)ᵀ) =
      Algebra.trace (AF F) (AE F E) Z := by unfold spf_k symp; rw [_root_.GlobalTheory.ThK.Dbl.Dense.hTens_tr, neg_one_mul]
  rw [hsp, d.std.2.2 _ (Place.at_of_finOne hf')]
  have hev : evI F (-(⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) Z)) =
      -(algebraMap ℝ (mixedEmbedding.mixedSpace F) (⅟2) * evI F (Algebra.trace (AF F) (AE F E) Z)) := by
    rw [← Psi.evI_half, ← Dense.evI_mul]; exact map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) _
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (-(⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) Z))) =
      -(∑ w, (piInf (d.B.emb w) Z).re) := by
    rw [hev, map_neg, ← Algebra.smul_def, LinearMap.map_smul, trace_evI_trace, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
    exact sum_congr rfl fun _ _ => by rw [invOf_eq_inv]; ring
  rw [htr]; congr 1
  have hfrm (w) : ((d.b.1.toCols₂).map (d.B.emb w).1)ᵀ * (dbl d.Y.J).map (d.B.emb w).1 *
      ((d.b.1.toCols₁).map (d.B.emb w).1).map star = (((R.ε : ℤ) : ℂ)) • 1 := by
    have h := congrArg (fun x => x.map (d.B.emb w).1) R.hε
    simp only [Matrix.map_mul, transpose_map] at h
    rw [show (d.b.1.map σ).map (d.B.emb w).1 = (d.b.1.map (d.B.emb w).1).map star from
      Matrix.ext fun _ _ => d.cm.2.2.2 (d.B.emb w).1 _] at h
    ext i j
    simpa [Matrix.mul_apply, Matrix.toCols₁, Matrix.toCols₂, Matrix.one_apply, Matrix.smul_apply, apply_ite]
      using congrFun (congrFun h (Sum.inr i)) (Sum.inl j)
  have heps : ((R.ε : ℤ) : ℂ) * star R.ζ * R.ζ⁻¹ = -1 := by rcases R.hζ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hdbl : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := Krd.dbl_incM_k d
  have hpi (w) : (piInf (d.B.emb w) Z).re =
      -(s * t) * ∑ i, ∑ j, ((R.loc w W i j).re * (R.loc w W i j).re + (R.loc w W i j).im * (R.loc w W i j).im) := by
    simp only [Z]; rw [map_neg]
    have htrw : piInf (d.B.emb w) ((((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
        ((realAd F t • tw_k R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ).trace) =
        ((s * t : ℝ) : ℂ) * ((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w W)).trace := by
      have hptr {ι : Type} [Fintype ι] (M : Matrix ι ι (AE F E)) : piInf (d.B.emb w) M.trace = (d.cw w M).trace := by
        simp only [Matrix.trace, Matrix.diag_apply, SD_k.cw, Matrix.map_apply, map_sum]
      rw [hptr]
      have hcw : d.cw w (((realAd F s • W) * (incM F d.b.1.toCols₂)ᵀ)ᵀ * incM F d.A.J *
          ((realAd F t • tw_k R W) * (incM F d.b.1.toCols₁)ᵀ).map (cA σ) * (dbl (incM F d.Y.J))ᵀ) =
          (((s : ℂ) • d.cw w W) * ((d.b.1.toCols₂).map (d.B.emb w).1)ᵀ)ᵀ * d.A.J.map (d.B.emb w).1 *
            ((((t : ℂ) * (-(((R.sg w : ℤ) : ℂ) * R.ζ))) • d.cw w W) *
              ((d.b.1.toCols₁).map (d.B.emb w).1)ᵀ).map star * ((dbl d.Y.J).map (d.B.emb w).1)ᵀ := by
        simp only [SD_k.cw, Matrix.map_mul, transpose_map]; rw [hdbl]
        have c1 := cw_realAd (d := d) w s W; have c2 := cw_realAd (d := d) w t (tw_k R W)
        have c3 : d.cw w (tw_k R W) = (-(((R.sg w : ℤ) : ℂ) * R.ζ)) • d.cw w W := (exists_tw_k R W).choose_spec.2 w
        have c4 := Krd.cw_incM_k d w d.A.J; have c5 := Krd.cw_incM_k d w d.b.1.toCols₁
        have c6 := Krd.cw_incM_k d w d.b.1.toCols₂; have c7 := Krd.cw_incM_k d w (dbl d.Y.J)
        have c8 := Place.cw_cA_k d w ((realAd F t • tw_k R W) * (incM F d.b.1.toCols₁)ᵀ)
        simp only [SD_k.cw, Matrix.map_mul, transpose_map] at c1 c2 c3 c4 c5 c6 c7 c8
        rw [c8, c1, c2, c3, c4, c5, c6, c7, smul_smul]
      rw [hcw, Psi.trace_line, hfrm, Matrix.transpose_smul, transpose_one, Matrix.mul_smul, Matrix.mul_one,
        trace_smul, ← KW.cw_gram_k, R.cw_gram w W, trace_smul, smul_eq_mul, smul_eq_mul]
      have e := heps; have sq := sg_sq R w
      push_cast; simp only [star_mul', star_neg, Complex.star_def, Complex.conj_ofReal, map_intCast]
      rw [Complex.star_def] at e
      linear_combination (-(s : ℂ) * t * (((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w W)).trace) *
        ((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * e +
        ((s : ℂ) * t * ((Matrix.of (R.loc w W))ᴴ * Matrix.of (R.loc w W)).trace) * sq
    rw [htrw, ← re_trace_loc, Complex.neg_re, Complex.re_ofReal_mul]; ring
  simp only [hpi]; rw [← Finset.mul_sum, ← inner_arc, real_inner_self_eq_norm_sq]; push_cast; ring
theorem om_rot_vac'_k (hT : TAll_k) (hLO : LocOpEx_k) (hLI : LocInst_k) (R : RD_k d) (t : ℝ) :
    ∃ χ : ℂ, χ ≠ 0 ∧ ∀ g ∈ SB (Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = vac_k R g → d.om (rot_k R t) Ω = χ • Ω := by
  have hpl (w : InfinitePlace F) : ∃ (p q : ℕ) (e : ℤ), ∀ y : GR d.n, InK (mR y) → ∀ g ∈ SB (Yf_k d), ∀ Ω ∈ d.sch,
      d.T Ω = vac_k R g → d.om (R.ι w y) Ω = F0 p q e y • Ω := by
    obtain ⟨L, hL⟩ := hLO F E σ d R w; obtain ⟨sL, ρ, p, q, e, -, hLD, -, hLk⟩ := hLI F E σ d R w L hL
    refine ⟨p, q, e, fun y hy g hg Ω hΩ hTΩ => ?_⟩
    let Ψ : M1 d → ℂ := fun X =>
      (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g (fun k => (d.crd X k).2)
    have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
    have hvt : d.T Ω = R.tens w (fP (1 : PX d.m d.n)) Ψ := by
      rw [hTΩ]; funext X; simp only [vac_k, gau_k, RD_k.tens, Ψ]
      rw [← Finset.mul_prod_erase Finset.univ (fun w' => fP (1 : PX d.m d.n) (R.loc w' X)) (Finset.mem_univ w),
        _root_.mul_assoc]; rfl
    have h1 := (hL y (fP (1 : PX d.m d.n)) (KFock.isSw_fP 1)).2 Ψ (KFock.away_inv_k R w Ψ hΨ) Ω hΩ hvt
    rw [hLk y 1 hy, hLD.kvac y hy,
      show fP (F0 p q e y • (1 : PX d.m d.n)) = F0 p q e y • fP (1 : PX d.m d.n) from funext fun _ => by
        simp only [fP, evX, MvPolynomial.smul_eq_C_mul, _root_.map_mul, MvPolynomial.eval_C, Pi.smul_apply,
          smul_eq_mul]; ring,
      show R.tens w (F0 p q e y • fP (1 : PX d.m d.n)) Ψ = F0 p q e y • R.tens w (fP (1 : PX d.m d.n)) Ψ from
        funext fun _ => by simp only [RD_k.tens, Pi.smul_apply, smul_eq_mul]; ring,
      ← hvt, ← KFock.T_smul_k] at h1
    exact KFock.T_inj_k hT.1 d (d.ok.dbl.weil.2.1.toIsSplitting.pres _ Ω hΩ) (d.sch.smul_mem _ hΩ) h1
  have key : ∀ l : List (InfinitePlace F), ∃ χ : ℂ, χ ≠ 0 ∧ ∀ g ∈ SB (Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = vac_k R g →
      d.om ((l.map fun w => R.ι w (yrot d.n (R.sg w) t)).prod) Ω = χ • Ω := fun l => by
    induction l with
    | nil => exact ⟨1, one_ne_zero, fun _ _ _ _ _ => by simp⟩
    | cons w l ih =>
      obtain ⟨χ, hχ, h⟩ := ih; obtain ⟨p, q, e, hw⟩ := hpl w
      refine ⟨F0 p q e (yrot d.n (R.sg w) t) * χ, mul_ne_zero (weight_factor_rotation_ne_zero p q e d.n (R.sg w) t) hχ,
        fun g hg Ω hΩ hTΩ => ?_⟩
      rw [List.map_cons, List.prod_cons, _root_.map_mul, mul_apply_eq_comp, h g hg Ω hΩ hTΩ, map_smul,
        hw _ (by rw [mR_yrot]; exact _root_.PositivityTheory.SiegelWeilFormula.KFP.inK_yrotM _ _ _) g hg Ω hΩ hTΩ, smul_smul, mul_comm]
  exact key _
end KFP

end PositivityTheory.SiegelWeilFormula
end
