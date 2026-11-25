module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentParamRationalMatrix
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfCells
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldSmallSTop
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DerivInv
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.IsExtAtOfDiff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.SectionEqThetaZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.FockOf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.UnitsBorelSpace.BorelSpaceDoubledGroup
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

/-! # SiegelWeilOswgenFockOf: Consolidated global theta-kernel definitions and proofs (SiegelWeilOswgenFockOf). -/
@[expose] public section

noncomputable section

section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont
  PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp
open Matrix (fromBlocks transpose_mul)
open Finset (sum_congr sum_eq_zero)
open Set (indicator_of_mem indicator_of_notMem)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace PositivityTheory.SiegelWeilFormula
section
namespace KFP.OswGen
variable {d : SD_k σ}
section
def zInv_k (z : InfinitePlace F → Fin d.m → Fin d.n → ℂ) : KFP.Iw_k d → ℝ :=
  fun i => if i.2.2.2 then (z i.1 i.2.1 i.2.2.1).re else (z i.1 i.2.1 i.2.2.1).im
variable (d) in
def zLE_k : (KFP.Iw_k d → ℝ) ≃ₗ[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) where
  toFun := KFP.zOf_k
  invFun := zInv_k
  map_add' u v := by
    funext w a j
    apply Complex.ext <;> simp [KFP.zOf_k]
  map_smul' c u := by
    funext w a j
    apply Complex.ext <;> simp [KFP.zOf_k]
  left_inv u := by
    funext i
    obtain ⟨w, a, j, b⟩ := i
    cases b <;> simp [KFP.zOf_k, zInv_k]
  right_inv z := by
    funext w a j
    apply Complex.ext <;> simp [KFP.zOf_k, zInv_k]
theorem hg_sch_k (R : RD_k d) {νf : Measure (KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : d.MxE → ℂ}
                        (hf : f ∈ d.schM)
    {g : KFP.Yf_k d → ℂ} (hg' : g ∈ SB (KFP.Yf_k d)) : ∃ h : 𝓢(KFP.Vw_k d, ℂ), ⇑h = KFP.hg_k R νf f g := by
  obtain ⟨L, hL⟩ := KFock.archEquiv_k d R
  let Zc :=
    (EuclideanSpace.equiv (KFP.Iw_k d) ℝ).trans (zLE_k d).toContinuousLinearEquiv
  let c : KFP.Vw_k d → KFP.Yf_k d → (d.I3 → AF F) := fun u y k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (Zc u) k)) (y k) : AF F)
  have hc1 : ∀ u y, (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c u y k).1) = L.symm (Zc u) := by
    intro u y
    funext k
    exact RingEquiv.apply_symm_apply _ _
  have hjn : ∀ u y, KFP.jn_k R u y = d.cmb (c u y) := by
    intro u y
    refine (KFP.exists_jn_k R u y).unique ⟨KFP.arc_jn_k R u y, KFP.fin_jn_k R u y⟩ ⟨?_, ?_⟩
    · rw [KFP.arc_eq_iff_k]
      intro w
      rw [← hL (c u y) w, hc1, ContinuousLinearEquiv.apply_symm_apply]
      rfl
    · funext k
      show (d.crd (d.cmb (c u y)) k).2 = y k
      rw [KFock.crd_cmb'_k]
  have := hνf
  have : BorelSpace (Af F) := ⟨rfl⟩
  have : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  have : BorelSpace (KFP.Yf_k d) := Pi.borelSpace
  have hint : ∀ g' ∈ SB (KFP.Yf_k d), Integrable (fun y => g' y * star (g y)) νf := by
    intro g' hg''
    have hc :=
      hg''.1.continuous.mul (continuous_star.comp hg'.1.continuous)
    exact hc.integrable_of_hasCompactSupport (hg''.2.mul_right (f' := fun y => star (g y)))
  have key : ∀ Φ ∈ schA F (d.I3), (∀ u, Integrable (fun y => Φ (c u y) * star (g y)) νf) ∧
      ∃ h : 𝓢(KFP.Vw_k d, ℂ), ∀ u, h u = ∫ y, Φ (c u y) * star (g y) ∂νf := by
    intro Φ hΦ
    unfold schA at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ hmem =>
      obtain ⟨φ, g', hg'', rfl⟩ := hmem
      have e : ∀ u y, pureA F φ g' (c u y) = φ (L.symm (Zc u)) * g' y := by
        intro u y
        simp only [pureA]
        rw [hc1]
      refine ⟨fun u => ?_, ⟨(∫ y, g' y * star (g y) ∂νf) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (Zc.trans L.symm) φ,
        fun u => ?_⟩⟩
      · simp only [e, mul_assoc]
        exact (hint g' hg'').const_mul _
      · simp only [e, mul_assoc, integral_const_mul, smul_apply,
          SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, ContinuousLinearEquiv.trans_apply,
          smul_eq_mul]
        ring
    | zero => exact ⟨fun u => by simp, 0, fun u => by simp⟩
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      obtain ⟨i1, k1, e1⟩ := h₁
      obtain ⟨i2, k2, e2⟩ := h₂
      refine ⟨fun u => ?_, k1 + k2, fun u => ?_⟩
      · simp only [Pi.add_apply, add_mul]
        exact (i1 u).add (i2 u)
      · simp only [Pi.add_apply, add_mul, add_apply, e1, e2]
        rw [integral_add (i1 u) (i2 u)]
    | smul a Φ _ h =>
      obtain ⟨i1, k1, e1⟩ := h
      refine ⟨fun u => ?_, a • k1, fun u => ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact (i1 u).const_mul a
      · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, smul_apply, e1, integral_const_mul]
  obtain ⟨-, h, eh⟩ := key (f ∘ d.cmb) hf
  refine ⟨h, funext fun u => ?_⟩
  rw [eh u]
  show _ = ∫ y, f (KFP.jn_k R u y) * star (g y) ∂νf
  simp only [hjn, Function.comp_apply]
end

section
variable (R : RD_k d)
theorem arc_apply_k (X : d.MxE) (i : KFP.Iw_k d) :
    KFP.arc_k R X i = if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im := rfl
theorem norm_arc_sq_k (X : d.MxE) :
    ‖KFP.arc_k R X‖ ^ 2 = ∑ w, ∑ a, ∑ j, ‖R.loc w X a j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, arc_apply_k, ite_true, Bool.false_eq_true, ite_false,
    Real.norm_eq_abs, sq_abs]
  refine sum_congr rfl fun w _ => sum_congr rfl fun a _ => sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring
theorem gauss_eq_k (X : d.MxE) :
    ((Real.exp (-(2 * Real.pi * ‖KFP.arc_k R X‖ ^ 2)) : ℝ) : ℂ) = ∏ w, gs (2 * Real.pi) (R.loc w X) := by
  rw [Complex.ofReal_exp, norm_arc_sq_k]
  simp only [gs]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_neg_distrib]
end
def lin_k (a : Fin d.m) (j : Fin d.n) (b : Bool) : PX d.m d.n :=
  if b then MvPolynomial.C (1 / 2) * (MvPolynomial.X (a, j, false) + MvPolynomial.X (a, j, true))
  else MvPolynomial.C (-Complex.I / 2) * (MvPolynomial.X (a, j, false) - MvPolynomial.X (a, j, true))
theorem evX_lin_k (a : Fin d.m) (j : Fin d.n) (b : Bool) (z : Fin d.m → Fin d.n → ℂ) :
    evX (lin_k a j b) z = ((if b then (z a j).re else (z a j).im : ℝ) : ℂ) := by
  cases b
  · simp only [lin_k, evX, Bool.false_eq_true, ite_false, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
      ite_true]
    apply Complex.ext <;> simp; ring
  · simp only [lin_k, evX, ite_true, Bool.false_eq_true, ite_false, map_mul, map_add (f := _), MvPolynomial.eval_C,
      MvPolynomial.eval_X]
    apply Complex.ext <;> simp; ring
theorem fP_mul_k (P Q : PX d.m d.n) (u : Fin d.m → Fin d.n → ℂ) : fP (P * Q) u = evX P u * fP Q u := by
  simp only [fP, evX, map_mul]
  ring
section
variable (R : RD_k d)
theorem mul_coord_mem_k (i : KFP.Iw_k d) {h : d.MxE → ℂ} (hh : h ∈ R.fock) :
    (fun X => ((KFP.arc_k R X i : ℝ) : ℂ) * h X) ∈ R.fock := by
  unfold RD_k.fock RD_k.fockOn at hh ⊢
  induction hh using Submodule.span_induction with
  | mem h hmem =>
    obtain ⟨P, g, hg, rfl⟩ := hmem
    apply Submodule.subset_span
    refine ⟨Function.update P i.1 (lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1), g, hg, ?_⟩
    funext X
    have e1 : ∏ w ∈ Finset.univ, fP (Function.update P i.1 (lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1) w) (R.loc w X) =
        fP (lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i.1), Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun w hw => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
    have e2 : ∏ w ∈ Finset.univ, fP (P w) (R.loc w X) =
        fP (P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i.1)).symm
    dsimp only
    rw [e1, e2, fP_mul_k, evX_lin_k, arc_apply_k]
    ring
  | zero =>
    convert Submodule.zero_mem _ using 1
    ext X
    simp
  | add h₁ h₂ _ _ i₁ i₂ =>
    convert Submodule.add_mem _ i₁ i₂ using 1
    funext X
    simp [mul_add]
  | smul a h _ i₁ =>
    convert Submodule.smul_mem _ a i₁ using 1
    ext X
    simp [smul_eq_mul, mul_comm, mul_assoc]
theorem poly_mem_k (Q : MvPolynomial (KFP.Iw_k d) ℂ) {g : KFP.Yf_k d → ℂ} (hg : g ∈ SB (KFP.Yf_k d)) :
    (fun X => MvPolynomial.eval (fun i => ((KFP.arc_k R X i : ℝ) : ℂ)) Q * (Real.exp (-(2 * Real.pi *
        ‖KFP.arc_k R X‖ ^ 2)) : ℂ) *
      g (KFP.fin_k d X)) ∈ R.fock := by
  have base : (fun X => (Real.exp (-(2 * Real.pi * ‖KFP.arc_k R X‖ ^ 2)) : ℂ) * g (KFP.fin_k d X)) ∈ R.fock := by
    unfold RD_k.fock RD_k.fockOn
    apply Submodule.subset_span
    refine ⟨fun _ => 1, g, hg, ?_⟩
    funext X
    rw [gauss_eq_k]
    simp only [fP, evX, map_one, one_mul]
    rfl
  induction Q using MvPolynomial.induction_on with
  | C a =>
    convert Submodule.smul_mem _ a base using 1
    ext X
    simp [smul_eq_mul, mul_assoc]
  | add p q hp hq =>
    convert Submodule.add_mem _ hp hq using 1
    ext X
    simp [add_mul]
  | mul_X p i hp =>
    convert mul_coord_mem_k R i hp using 1
    ext X
    simp only [map_mul, MvPolynomial.eval_X]
    ring

theorem crd_inf_eq_k 
    (L : (d.I3 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ))
    (hL : ∀ (c : d.I3 → AF F) (w : InfinitePlace F),
      L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) w = R.loc w (d.cmb c)) (X : d.MxE) :
    (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) =
      L.symm (((EuclideanSpace.equiv (KFP.Iw_k d) ℝ).trans (zLE_k d).toContinuousLinearEquiv) (KFP.arc_k R X)) := by
  apply L.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext w
  rw [hL, KFock.cmb_crd_k]
  exact (KFP.arc_eq_iff_k R X (KFP.arc_k R X)).1 rfl w
theorem mem_fock_of_k {νf : Measure (KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : d.MxE → ℂ}
    (hf : f ∈ d.schM) (H : ∀ g ∈ SB (KFP.Yf_k d), ∃ P : MvPolynomial (KFP.Iw_k d) ℂ,
      ∀ u, KFP.hg_k R νf f g u = MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) :
    f ∈ R.fock := by
  obtain ⟨L, hL⟩ := KFock.archEquiv_k d R
  set Zc : KFP.Vw_k d ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
    (EuclideanSpace.equiv (KFP.Iw_k d) ℝ).trans (zLE_k d).toContinuousLinearEquiv with hZc
  have hΦ : f ∘ d.cmb ∈ Submodule.span ℂ {Φ | ∃ (φ : SchwartzMap (d.I3 →
      mixedEmbedding.mixedSpace F) ℂ)
      (g : (d.I3 → FiniteAdeleRing (𝓞 F) F) → ℂ),
      g ∈ SB (d.I3 → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F φ g} := hf
  obtain ⟨N, a, x, hx⟩ := Submodule.mem_span_set'.1 hΦ
  choose φ gg hgg hxeq using fun i => (x i).2
  have hfX : ∀ X, f X = ∑ i, a i * (φ i (L.symm (Zc (KFP.arc_k R X))) * gg i (KFP.fin_k d X)) := by
    intro X
    have e1 : f X = (f ∘ d.cmb) (d.crd X) := by simp [KFock.cmb_crd_k]
    rw [e1, ← hx, Finset.sum_apply]
    refine sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, hxeq i, smul_eq_mul]
    congr 1
    simp only [pureA]
    rw [crd_inf_eq_k R L hL X]
    rfl
  have hfjn : ∀ u y, f (KFP.jn_k R u y) = ∑ i, a i * (φ i (L.symm (Zc u)) * gg i y) := by
    intro u y
    rw [hfX, KFP.arc_jn_k, KFP.fin_jn_k]
  let Φv : KFP.Yf_k d → (Fin N → ℂ) := fun y i => gg i y
  have hloc : IsLocallyConstant Φv := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_
    have h := Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (hgg i).1 y
    filter_upwards [h] with z hz
    funext i
    exact hz i
  set K : Set (KFP.Yf_k d) := ⋃ i, tsupport (gg i) with hK
  have hKc : IsCompact K := isCompact_iUnion fun i => (hgg i).2
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun c : Fin N → ℂ => {y | Φv y = c}) (fun c => hloc.isOpen_fiber c)
    (fun y _ => Set.mem_iUnion.2 ⟨Φv y, rfl⟩)
  set Vals := t.filter (fun c => c ≠ 0) with hVals
  have hfib_sub : ∀ c : Fin N → ℂ, c ≠ 0 → {y | Φv y = c} ⊆ K := by
    intro c hc y hy
    by_contra hyK
    apply hc
    rw [← show Φv y = c from hy]
    funext i
    show gg i y = 0
    exact image_eq_zero_of_notMem_tsupport (f := gg i) fun h => hyK (Set.mem_iUnion.2 ⟨i, h⟩)
  have := hνf
  have : BorelSpace (Af F) := ⟨rfl⟩
  have : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  have : BorelSpace (KFP.Yf_k d) := Pi.borelSpace
  let ψ : (Fin N → ℂ) → KFP.Vw_k d → ℂ := fun c u => ∑ i, a i * (φ i (L.symm (Zc u)) * c i)
  have hterm : ∀ c ∈ Vals, (fun X => ψ c (KFP.arc_k R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ))
      (KFP.fin_k d X)) ∈ R.fock := by
    intro c hc
    have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
    set Nc : Set (KFP.Yf_k d) := {y | Φv y = c} with hNc
    have hNo : IsOpen Nc := hloc.isOpen_fiber c
    have hNcl : IsClosed Nc := hloc.isClosed_fiber c
    have hNk : IsCompact Nc := hKc.of_isClosed_subset hNcl (hfib_sub c hc0)
    rcases Nc.eq_empty_or_nonempty with he | hne
    · have : (fun X => ψ c (KFP.arc_k R X) * Nc.indicator (fun _ => (1 : ℂ)) (KFP.fin_k d X)) = 0 := by
        funext X
        rw [he, Set.indicator_empty, mul_zero]
        rfl
      rw [this]
      exact Submodule.zero_mem _
    · have hSB := indicator_mem_SB hNo hNcl hNk
      obtain ⟨P, hP⟩ := H _ hSB
      have hm0 : 0 < νf.real Nc := by
        rw [measureReal_def]
        exact ENNReal.toReal_pos (hNo.measure_pos νf hne).ne' hNk.measure_lt_top.ne
      have hval : ∀ u, KFP.hg_k R νf f (Nc.indicator fun _ => (1 : ℂ)) u = ψ c u * (νf.real Nc : ℂ) := by
        intro u
        have e : (fun y => f (KFP.jn_k R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y)) =
            Nc.indicator (fun _ => ψ c u) := by
          funext y
          by_cases hy : y ∈ Nc
          · rw [indicator_of_mem hy, indicator_of_mem hy, star_one, mul_one, hfjn]
            have hy' : ∀ i, gg i y = c i := fun i => congrFun hy i
            simp only [ψ, hy']
          · rw [indicator_of_notMem hy, indicator_of_notMem hy, star_zero, mul_zero]
        show ∫ y, f (KFP.jn_k R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y) ∂νf = _
        rw [e, integral_indicator_const _ hNo.measurableSet, Complex.real_smul, mul_comm]
      have hψ : ∀ u, ψ c u = ((νf.real Nc)⁻¹ : ℂ) *
          (MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) := by
        intro u
        rw [← hP u, hval u]
        have : (νf.real Nc : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm0.ne'
        field_simp
      have e2 : (fun X => ψ c (KFP.arc_k R X) * Nc.indicator (fun _ => (1 : ℂ)) (KFP.fin_k d X)) =
          ((νf.real Nc)⁻¹ : ℂ) • (fun X => MvPolynomial.eval (fun i => ((KFP.arc_k R X i : ℝ) : ℂ)) P *
            (Real.exp (-(2 * Real.pi * ‖KFP.arc_k R X‖ ^ 2)) : ℂ) * Nc.indicator (fun _ => (1 : ℂ)) (KFP.fin_k d X)) :=
                by
        funext X
        simp only [Pi.smul_apply, smul_eq_mul, hψ]
        ring
      rw [e2]
      exact Submodule.smul_mem _ _ (poly_mem_k R P hSB)
  have hsum : f = ∑ c ∈ Vals, (fun X => ψ c (KFP.arc_k R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ))
      (KFP.fin_k d X)) := by
    funext X
    rw [Finset.sum_apply, hfX]
    by_cases h0 : Φv (KFP.fin_k d X) = 0
    · have hz : ∀ i, gg i (KFP.fin_k d X) = 0 := fun i => congrFun h0 i
      simp only [hz, mul_zero, Finset.sum_const_zero]
      refine (sum_eq_zero fun c hc => ?_).symm
      have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
      have : KFP.fin_k d X ∉ {y | Φv y = c} := fun h => hc0 (h.symm.trans h0)
      rw [indicator_of_notMem this, mul_zero]
    · have hmemK : KFP.fin_k d X ∈ K := hfib_sub _ h0 rfl
      have hmemt : Φv (KFP.fin_k d X) ∈ t := by
        have := ht hmemK
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at this
        obtain ⟨c, hct, hc⟩ := this
        rw [hc]
        exact hct
      have hmemV : Φv (KFP.fin_k d X) ∈ Vals := Finset.mem_filter.2 ⟨hmemt, h0⟩
      rw [Finset.sum_eq_single_of_mem _ hmemV]
      · rw [indicator_of_mem (show KFP.fin_k d X ∈ {y | Φv y = Φv (KFP.fin_k d X)} from rfl), mul_one]
      · intro c _ hne
        have : KFP.fin_k d X ∉ {y | Φv y = c} := fun h => hne h.symm
        rw [indicator_of_notMem this, mul_zero]
  rw [hsum]
  exact Submodule.sum_mem _ hterm
end
end KFP.OswGen
end
namespace AStep
namespace COneB
variable {d : SD_k σ} (L : LD_k d)
theorem uM_add_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u v : Fin L.n → AE F E) : uM (u + v) = uM u * uM v := by
  rw [Afc.uM_eq_k L hu, Afc.unipotentOfVector_add]
theorem uM_zero_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) : uM 0 = 1 := by
  rw [Afc.uM_eq_k L hu, Afc.unipotentOfVector_zero]
theorem uM_neg_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : (uM u)⁻¹ = uM (-u) := by
  have h := uM_add_k L hu (-u) u; rw [neg_add_cancel, uM_zero_k L hu] at h
  exact (eq_inv_of_mul_eq_one_left h.symm).symm
theorem uM_cont_k {uM ν 𝓤} (hu : L.UData uM ν 𝓤) : Continuous uM :=
  Act.ComplexParameterFamilyContinuity.continuous_uM_k L hu
theorem ratV_cocompact_k : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ u, ∃ r ∈ L.ratV, r + u ∈ K :=
  Afc.ratV_cocompact_k L
set_option linter.defProp false in
def fcBd'_k (d : SD_k σ) {nb lam 𝓖} (hc : d.CD nb lam 𝓖) (T : d.nF_) :=
  kfour.fcBd'_core_k d hc T
end COneB
section Deg
variable (H : Hyps_k) {d : SD_k σ} (R : RD_k d) (L : LD_k d) (R' : RD_k L.sd) (hmn : d.m < d.n) (hIH : MainV_k 2 R')
  {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ} (hE :
  EData_k d (d.sec0 Φ) d.s₀ d.s₀ U p Ê t)
include H hE in
theorem avgHol_k {nb lam 𝓖} (hc : d.CD nb lam 𝓖) (T : d.nF_) {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (x : d.G) :
    DifferentiableOn ℂ (fun z => avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) U ∧ ∀ i : ℕ,
      iteratedDeriv i (fun z => avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) d.s₀ =
        avg_k d L uM ν 𝓤 nb lam 𝓖 (fun g => iteratedDeriv i (Ê · g) d.s₀) T x := by
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  have hσ := kfour.sigma_sigma_of_good_k d.ok.good
  have hb := d.ok.frame
  have hnbc := kfour.nb_continuous hσ hb hc.1
  obtain ⟨iTG, -, -, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  obtain ⟨KN, hKN, hKNb⟩ := COneB.fcBd'_k d hc T
  obtain ⟨KU, hKU, hKUc⟩ := COneB.ratV_cocompact_k L
  have huc := COneB.uM_cont_k L hu
  let C : Set d.G := (fun q : d.nA_ × (Fin L.n → AE F E) => nb q.1 * uM q.2 * x) '' (KN ×ˢ KU)
  have hCc : IsCompact C :=
    (hKN.prod hKU).image (((hnbc.comp continuous_fst).mul (huc.comp continuous_snd)).mul continuous_const)
  have hper : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ d.r2, ∀ g, φ (γ * g) = φ g) → ∀ u, ∃ k ∈ KU,
      fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T (uM k * x) := by
    intro φ hφ hi u
    obtain ⟨r, hr, hk⟩ := hKUc u
    refine ⟨r + u, hk, ?_⟩
    rw [COneB.uM_add_k L hu, mul_assoc, (H.fcConj F E σ d L nb lam 𝓖 hc).2 uM ν 𝓤 hu T T' hT φ hφ hi r hr]
  have hbound : ∀ (φ : d.G → ℂ) (M : ℝ), Continuous φ → (∀ γ ∈ d.r2, ∀ g, φ (γ * g) = φ g) →
      (∀ y ∈ C, ‖φ y‖ ≤ M) → ∀ u, ‖fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)‖ ≤ M := by
    intro φ M hφ hi hM u
    obtain ⟨k, hk, e⟩ := hper φ hφ hi u
    rw [e]
    refine hKNb φ M hi _ fun β hβ => hM _ ⟨(β, k), ⟨hβ, hk⟩, ?_⟩
    simp only [mul_assoc]
  have hmeas : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ d.r2, ∀ g, φ (γ * g) = φ g) →
      AEStronglyMeasurable (fun u => fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)) ν := by
    intro φ hφ hi
    exact ((fcCont_k d hc T φ hφ hi).comp (huc.mul continuous_const)).aestronglyMeasurable
  have hfin : ν 𝓤 < ⊤ := by rw [hu.2.2.2]; exact ENNReal.one_lt_top
  have hint : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ d.r2, ∀ g, φ (γ * g) = φ g) →
      IntegrableOn (fun u => fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)) 𝓤 ν := by
    intro φ hφ hi
    obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn hφ.continuousOn
    exact Measure.integrableOn_of_bounded (M := M) hfin.ne (hmeas φ hφ hi)
      (Filter.Eventually.of_forall fun u => hbound φ M hφ hi hM u)
  have hadd : ∀ (a : ℂ) (f f' : d.G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ d.r2, ∀ g, f (γ * g) = f g) →
      (∀ γ ∈ d.r2, ∀ g, f' (γ * g) = f' g) → avg_k d L uM ν 𝓤 nb lam 𝓖 (a • f + f') T x =
        a * avg_k d L uM ν 𝓤 nb lam 𝓖 f T x + avg_k d L uM ν 𝓤 nb lam 𝓖 f' T x := by
    intro a f f' hf hf' hi hi'
    simp only [avg_k]
    have e : (fun u => fc d.B.ψ d.b nb lam 𝓖 (a • f + f') T (uM u * x)) =
        fun u => a * fc d.B.ψ d.b nb lam 𝓖 f T (uM u * x) + fc d.B.ψ d.b nb lam 𝓖 f' T (uM u * x) :=
      funext fun u => (fcAll_k d hc T (uM u * x)).1 a f f' hf hf' hi hi'
    rw [e, integral_add ((hint f hf hi).const_mul a) (hint f' hf' hi'), integral_const_mul]
  have hbd : ∃ C : Set d.G, IsCompact C ∧ ∀ (f : d.G → ℂ) (M : ℝ), Continuous f →
      (∀ γ ∈ d.r2, ∀ g, f (γ * g) = f g) → (∀ y ∈ C, ‖f y‖ ≤ M) → ‖avg_k d L uM ν 𝓤 nb lam 𝓖 f T x‖ ≤ M := by
    refine ⟨C, hCc, fun f M hf hi hM => ?_⟩
    have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun u _ => hbound f M hf hi hM u)
    have hr : ν.real 𝓤 = 1 := by simp [Measure.real, hu.2.2.2]
    rw [hr, mul_one] at h1
    exact h1
  obtain ⟨hDiff, hComm⟩ := _root_.GlobalTheory.CompanionTheory.HolFamily.functional_commutes_iteratedDeriv d.r2 (fun φ =>
      avg_k d L uM ν 𝓤 nb lam 𝓖 φ T x) hadd hbd U Ê hUo hd hcont hinv
  exact ⟨hDiff, fun i => hComm _ hs i⟩
end Deg
namespace COne
section
variable (d : SD_k σ)
theorem om_sch_k (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ h
theorem T_zero_k {Φ : d.Fn} (h : Φ ∈ d.sch) : d.T Φ 0 = d.l Φ := (l_eq_T_k d Φ h).symm
theorem constantTerm_eq_fourierAtZero {Φ : d.Fn} (h : Φ ∈ d.sch) (x : d.G) : d.sec0 Φ x = d.T
    (d.om x Φ) 0 :=
  (T_zero_k d (om_sch_k d x h)).symm
theorem T_smul_k (c : ℂ) (Φ : d.Fn) (X : d.MxE) : d.T (c • Φ) X = c * d.T Φ X := by
  unfold SD_k.T Darboux.rho
  have : schr d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ)) (c • Φ) = c • schr d.B.ψ (d.dd.e (X *
      (incM F d.b.1.toCols₂)ᵀ)) Φ := by
    funext y; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
  rw [this, map_smul, smul_eq_mul]
theorem orb_smul_k (T : d.nF_) (c : ℂ) (Φ : d.Fn) : d.orb T (c • Φ) = c * d.orb T Φ := by
  unfold SD_k.orb
  simp only [T_smul_k, tsum_mul_left]
  simp only [MeasureTheory.average]
  exact integral_const_mul _ _
end
theorem Ln_k {d : SD_k σ} (L : LD_k d) : L.n + 1 = d.n := by
  have e : Fin L.n ≃ {i : Fin d.n // ¬ i = L.i₀} :=
    (Equiv.ofInjective L.em L.inj).trans (Equiv.subtypeEquivRight fun i => (L.rng i).symm)
  have h1 := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq] at h1
  have := L.i₀.isLt
  omega
theorem fcVal_k (H : AStep.Hyps_k) {d' : SD_k σ} (R'' : RD_k d') (hMV : MainV_k 2 R'') {Ψ : d'.Fn} (hΨ : Ψ ∈ d'.sch)
    (hv : d'.T Ψ ∈ R''.vac) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d'.Y) d'.b nb lam 𝓖) (T : nF σ d'.Y d'.b)
    (g : d'.G) :
    HolValueAt (fun z => fc d'.B.ψ d'.b nb lam 𝓖 (d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z) T g) (s0 d'.m d'.n)
      (2 * fc d'.B.ψ d'.b nb lam 𝓖 (d'.I Ψ) T g) := by
  have hK := H.polyKFin F E σ d' R'' Ψ hΨ ((H.vacK F E σ d' R'').2.1 hv)
  have hsec := H.secK F E σ d' Ψ hK
  obtain ⟨U, p, Ê, t, hE⟩ := H.eisWk F E σ d' _ _ hsec (s0 d'.m d'.n)
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hadd, hbd⟩ := fcAll_k d' hc T g
  obtain ⟨hDiff, hComm⟩ := _root_.GlobalTheory.CompanionTheory.HolFamily.functional_commutes_iteratedDeriv (rat2 σ d'.Y) (fun f =>
      fc d'.B.ψ d'.b nb lam 𝓖 f T g) hadd hbd U Ê hUo hd hcont hinv
  have hpt : ∀ g', ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n), iteratedDeriv i (Ê · g') (s0 d'.m d'.n) =
      iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * d'.I Ψ g') := fun g' =>
    ordVal U p (Ê · g') (fun z => d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z g') t _ (2 * d'.I Ψ g') hUo hR hs hp (hd g')
      (fun z hz => (hfar z hz).2 g') (hMV Ψ hΨ hv g')
  have hsm : ∀ (c : ℂ) (φ : d'.G → ℂ), fc d'.B.ψ d'.b nb lam 𝓖 (fun g' => c * φ g') T g =
      c * fc d'.B.ψ d'.b nb lam 𝓖 φ T g := by
    intro c φ; simp only [fc, mul_assoc]; exact integral_const_mul _ _
  have hder : ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n),
      iteratedDeriv i (fun z => fc d'.B.ψ d'.b nb lam 𝓖 (Ê z) T g) (s0 d'.m d'.n) =
        iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * fc d'.B.ψ d'.b nb lam 𝓖 (d'.I Ψ) T g) := by
    intro i hi
    rw [hComm _ hs i]
    have : (fun g' => iteratedDeriv i (Ê · g') (s0 d'.m d'.n)) =
        fun g' => (iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * 2) * d'.I Ψ g' :=
      funext fun g' => by rw [hpt g' i hi]; ring
    rw [this, hsm]; ring
  refine wrap U p _ _ t _ _ hUo hR hs hp hDiff (fun z hz => ?_) (fun i hi => ?_) (hder _ le_rfl)
  · have e1 := funext (hfar z hz).2
    rw [e1, hsm]
  · rw [hder i hi.le, pderiv_lt p _ i hi, zero_mul]
end COne
section Deg
variable (H : Hyps_k) {d : SD_k σ} (R : RD_k d) (L : LD_k d) (R' : RD_k L.sd) (hmn : d.m < d.n) (hIH : MainV_k 2 R')
  {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ} (hE :
  EData_k d (d.sec0 Φ) d.s₀ d.s₀ U p Ê t)
include H hIH hΦ hv in
theorem cOneVal_k {nb lam 𝓖} (hc : d.CD nb lam 𝓖) {nb' lam' 𝓖'}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : d.nF_} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
        (x : d.G) :
    HolValueAt (fun z => cOne_k d L (d.sec0 Φ) d.s₀ z nb' lam' 𝓖' T' x) d.s₀
      (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x) := by
  obtain ⟨q, g₀, k, r, c, hk, hx, hr, ha, hTq⟩ := H.iwaQ F E σ d L x
  have hΦk := COne.om_sch_k d k hΦ
  have hvk := (H.vacK F E σ d R).1 Φ hΦ hv k hk
  obtain ⟨Φ', hres, hv'⟩ := (H.vacK F E σ d R).2.2 L R' _ hΦk hvk
  have hΦ' : Φ' ∈ L.sd.sch := hres.1
  have hres0 : ∀ g : L.sd.G, L.sd.T (L.sd.om g Φ') 0 = d.T (d.om (L.j g) (d.om k Φ)) 0 := by
    intro g
    have := L.res _ hΦk Φ' hΦ' hres.2 g 0 (fun a => rfl)
    rwa [Matrix.submatrix_zero] at this
  have hf : ∀ g' : L.sd.G, d.sec0 Φ (L.j g' * x) = c * L.sd.sec0 Φ' (g' * g₀) := by
    intro g'
    have hΨ : d.om (L.j g₀) (d.om k Φ) ∈ d.sch := COne.om_sch_k d _ hΦk
    rw [COne.constantTerm_eq_fourierAtZero d hΦ, COne.constantTerm_eq_fourierAtZero L.sd hΦ', hx]
    have e : d.om (L.j g' * (q * L.j g₀ * k)) Φ = d.om (L.j g' * q) (d.om (L.j g₀) (d.om k Φ)) := by
      simp only [map_mul, mul_assoc]; rfl
    rw [e, hTq _ hΨ g' 0 (fun a => rfl), hres0 (g' * g₀)]
    congr 2
    simp only [map_mul]; rfl
  have hs' : s0 d.m L.n = s0 d.m d.n + 1 / 2 := by
    unfold s0; rw [← COne.Ln_k L]; push_cast; ring
  have hid : ∀ z, cOne_k d L (d.sec0 Φ) d.s₀ z nb' lam' 𝓖' T' x = (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
      fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2)) T' g₀ := by
    intro z
    have ex : z + 1 / 2 - s0 d.m L.n = z - s0 d.m d.n := by rw [hs']; ring
    have hF : ∀ g' : L.sd.G, ((d.Ht (L.j g' * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g' * x) =
        (c * (r : ℂ) ^ (z - s0 d.m d.n)) * (((L.sd.Ht (g' * g₀) : ℝ) : ℂ) ^ (z + 1 / 2 - s0 d.m L.n) *
          L.sd.sec0 Φ' (g' * g₀)) := by
      intro g'
      rw [hf g', ex]
      have e1 : ((d.Ht (L.j g' * x) : ℝ) : ℂ) = ((((r * L.a (g' * g₀)).toNNReal : ℝ)) : ℂ) := by
        simp only [SD_k.Ht, ha g']
      rw [e1, COne.ht_cpow r _ hr]
      simp only [SD_k.Ht]
      ring
    have hcs : GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) (fun g => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^
        (z - s0 d.m d.n) *
        d.sec0 Φ (L.j g * x)) = fun g => (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
          L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2) (g * g₀) :=
      funext fun g => COne.cosetSum_factor _ _ _ _ _ g₀ hF g
    unfold cOne_k
    rw [hcs]
    simp only [fc, mul_one, mul_assoc, integral_const_mul]
  have hW := COne.fcVal_k H R' hIH hΦ' hv' hc' T' g₀
  rw [hs'] at hW
  have hsh := COne.hv_shift _ d.s₀ (1 / 2) _ c r hr hW
  have hv1 : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = c * fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.I Φ') T' g₀ := by
    rw [H.thetaCoef F E σ d Φ hΦ nb lam 𝓖 hc T x, H.thetaCoef F E σ L.sd Φ' hΦ' nb' lam' 𝓖' hc' T' g₀]
    rw [(H.orbRes F E σ d).2 L T T' hT (d.om x Φ) (c • L.sd.om g₀ Φ') ⟨?_, ?_⟩, COne.orb_smul_k]
    · exact Submodule.smul_mem _ _ (COne.om_sch_k L.sd g₀ hΦ')
    · intro X hX
      rw [COne.T_smul_k]
      have h1 := L.res _ hΦk Φ' hΦ' hres.2 g₀ X hX
      have hΨ := COne.om_sch_k d (L.j g₀) hΦk
      have h2 := hTq _ hΨ 1 X hX
      simp only [map_one, one_mul, one_apply_eq_self] at h2
      have h1' : L.sd.T (L.sd.om g₀ Φ') (X.submatrix id L.em) = d.T (d.om (L.j g₀) (d.om k Φ)) X := h1
      rw [h1', hx]
      have e : d.om (q * L.j g₀ * k) Φ = d.om q (d.om (L.j g₀) (d.om k Φ)) := by simp only [map_mul]; rfl
      rw [e, h2]
  have hfun : (fun z => cOne_k d L (d.sec0 Φ) d.s₀ z nb' lam' 𝓖' T' x) = fun z => (c * (r : ℂ) ^
      (z - s0 d.m d.n)) *
      (fun z => fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m d.n + 1 / 2) z) T' g₀) (z + 1 / 2) := by
    funext z; rw [hid z, hs']
  rw [hfun, hv1]
  convert hsh using 1
  ring
end Deg
end AStep
end PositivityTheory.SiegelWeilFormula
end
end
