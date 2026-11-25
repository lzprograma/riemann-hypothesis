module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgePot
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeAnalytic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem exists_sheet_of_atlas {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    (q : X → Fin e → ℂ) (U : Set X) (lift : X → (Σ k, ι k) → ℂ)
    (L : Fin e → HermLine ι) (r : Fin e → ℝ)
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j))
    (x : X) (hUopen : IsOpen U) (hxU : x ∈ U)
    (hlift_mem : ∀ x' ∈ U, lift x' ∈ mcPts P)
    (hQa : AnalyticAt ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x))
    (hQd : (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x)).det ≠ 0)
    (hlift_an : AnalyticAt ℂ (lift ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x))
    (hseg_an : AnalyticAt ℂ ((fun x' => Ψ (segre (lift x'))) ∘ (A.chart (chartIdx A x)).symm)
      (A.chart (chartIdx A x) x))
    (hψ0u : Ψ (segre (lift x)) 0 ≠ 0)
    (hq_eq : ∀ x' ∈ U, q x' = fun i : Fin e => Ψ (segre (lift x')) i.succ / Ψ (segre (lift x')) 0) :
    ∃ γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ,
      IsSheet P Ψ (q x) ((Ψ (segre (lift x)) 0)⁻¹ • segre (lift x)) γ ∧
      (∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ γ (q x) = bsmul c (lift x)) ∧
      maDensity (fun i y' => r i * Real.log ((L i).h (γ y'))) (q x) =
        ReciprocityTheory.AnForm.maDens
          (fun i v => r i * Real.log ((L i).h (lift ((A.chart (chartIdx A x)).symm v))))
          (A.chart (chartIdx A x) x) /
          ‖LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A x)).symm) (A.chart (chartIdx A x) x) :
            (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by
  classical
  obtain ⟨k0⟩ := hP.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  set j := chartIdx A x with hjdef
  have hj : x ∈ (A.chart j).source := Classical.choose_spec (A.cover x)
  set u := A.chart j x with hudef
  have hsu : (A.chart j).symm u = x := (A.chart j).left_inv hj
  have huU : u ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact hxU⟩
  set Q := q ∘ (A.chart j).symm with hQdef
  set Df := fderiv ℂ Q u with hDf
  have hdet : Df.det ≠ 0 := hQd
  set Ce := Df.toContinuousLinearEquivOfDetNeZero hdet with hCe
  have hCe' : (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = Df :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero Df hdet
  have hstrict : HasStrictFDerivAt Q (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) u := by
    rw [hCe']; exact hQa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph Q with hF
  have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = Q := hstrict.toOpenPartialHomeomorph_coe
  have hus : u ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hyt : Q u ∈ F.target := hstrict.image_mem_toOpenPartialHomeomorph_target
  have hσu : F.symm (Q u) = u := by
    have := F.left_inv hus
    rwa [hFc] at this
  have hy0 : Q u = q x := by simp only [hQdef, Function.comp_apply, hsu]
  have hσa : AnalyticAt ℂ F.symm (Q u) := by
    refine F.analyticAt_symm (i := Ce) hyt ?_ ?_
    · rw [hσu, hFc]; exact hQa
    · rw [hσu, hFc, hCe']
  have hσd : HasFDerivAt F.symm (Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (Q u) := by
    refine F.hasFDerivAt_symm hyt ?_
    rw [hσu, hFc, hCe']
    exact hQa.differentiableAt.hasFDerivAt
  set γ₀ : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun y' => lift ((A.chart j).symm (F.symm y')) with hγ₀
  have hγ₀a : AnalyticAt ℂ γ₀ (Q u) := hlift_an.comp_of_eq hσa hσu
  have hγ₀u : γ₀ (Q u) = lift x := by simp only [hγ₀, hσu, hsu]
  set ψ0 : (Fin e → ℂ) → ℂ := fun y' => Ψ (segre (γ₀ y')) 0 with hψ0
  have hψ0a : AnalyticAt ℂ ψ0 (Q u) :=
    analyticAt_pi_iff.mp (hseg_an.comp_of_eq hσa hσu) 0
  have hψ0u' : ψ0 (Q u) ≠ 0 := by simp only [hψ0, hγ₀u]; exact hψ0u
  set c : (Fin e → ℂ) → K → ℂ := fun y' => Function.update (fun _ => (1 : ℂ)) k0 (ψ0 y')⁻¹
    with hcdef
  have hc_ne : ∀ y', ψ0 y' ≠ 0 → ∀ k, c y' k ≠ 0 := by
    intro y' h k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h]
    · simp [hcdef, Function.update_of_ne hk]
  have hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) (Q u) := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp only [hcdef, Function.update_self]; exact hψ0a.inv hψ0u'
    · simp only [hcdef, Function.update_of_ne hk]; exact analyticAt_const
  set γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => bsmul (c y') (γ₀ y') with hγdef
  have hγa : AnalyticAt ℂ γ (Q u) :=
    analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ₀a p)
  have hprod : ∀ y', ∏ k, c y' k = (ψ0 y')⁻¹ := fun y' => by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hseg : ∀ y', segre (γ y') = (ψ0 y')⁻¹ • segre (γ₀ y') := fun y' => by
    rw [← hprod y']; exact segre_smul (c y') (γ₀ y')
  refine ⟨γ, ⟨?_, ?_⟩, ⟨c (Q u), hc_ne _ hψ0u', by rw [← hy0]; simp only [hγdef, hγ₀u]⟩, ?_⟩
  · rw [← hy0, hseg]
    simp only [hψ0, hγ₀u]
  · rw [← hy0]
    have hU : ∀ᶠ y' in 𝓝 (Q u),
        F.symm y' ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
      hσa.continuousAt.preimage_mem_nhds (by
        rw [hσu]; exact ((A.chart j).isOpen_inter_preimage_symm hUopen).mem_nhds huU)
    filter_upwards [hγa.eventually_analyticAt, hU, F.open_target.mem_nhds hyt,
      hψ0a.continuousAt.eventually_ne hψ0u'] with y' ha hUy ht h0
    refine ⟨ha.differentiableAt, mcPts_smul hPh (c y') (hc_ne y' h0) (hlift_mem _ hUy.2), ?_⟩
    have hq : Q (F.symm y') = y' := by
      have := F.right_inv ht
      rwa [hFc] at this
    rw [hQdef, Function.comp_apply, hq_eq _ hUy.2] at hq
    rw [hseg, map_smul]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
      exact inv_mul_cancel₀ h0
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [← congrFun hq i, div_eq_inv_mul]
  · rw [← hy0]
    have hblk : ∀ k, ∃ i, γ₀ (Q u) ⟨k, i⟩ ≠ 0 := by
      rw [hγ₀u]; exact (hlift_mem x hxU).1
    have hH : ∀ i, cxHessian (fun y' => r i * Real.log ((L i).h (γ y'))) (Q u) =
        cxHessian (fun y' => r i * Real.log ((L i).h (γ₀ y'))) (Q u) := by
      intro i
      set G : (Fin e → ℂ) → ℂ :=
        fun y' => ((-(r i * ((L i).a k0 : ℝ)) : ℝ) : ℂ) * Complex.log (ψ0 y' / ψ0 (Q u)) with hG
      set C : ℝ := -(r i * ((L i).a k0 : ℝ) * Real.log ‖ψ0 (Q u)‖) with hC
      have hGa : AnalyticAt ℂ G (Q u) := by
        refine analyticAt_const.mul ((hψ0a.div analyticAt_const hψ0u').clog ?_)
        show ψ0 (Q u) / ψ0 (Q u) ∈ Complex.slitPlane
        rw [div_self hψ0u']
        exact Complex.one_mem_slitPlane
      have heq : (fun y' => r i * Real.log ((L i).h (γ y'))) =ᶠ[𝓝 (Q u)]
          fun y' => r i * Real.log ((L i).h (γ₀ y')) + (G y').re + C := by
        filter_upwards [hψ0a.continuousAt.eventually_ne hψ0u',
          hγ₀a.continuousAt.eventually (isOpen_blockNonzero.mem_nhds hblk)] with y' h0 hb
        have hpos : 0 < (L i).h (γ₀ y') := (L i).pos _ hb
        have hn0 : ‖(ψ0 y')⁻¹‖ ^ (L i).a k0 ≠ 0 :=
          zpow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero h0))
        simp only [hγdef]
        rw [show bsmul (c y') (γ₀ y') = fun p => c y' p.1 * γ₀ y' p from rfl,
          (L i).smul _ _ (hc_ne y' h0),
          Finset.prod_eq_single_of_mem k0 (Finset.mem_univ k0) fun k _ hk => by simp [hcdef, hk],
          show c y' k0 = (ψ0 y')⁻¹ from Function.update_self .., Real.log_mul hn0 hpos.ne',
          hG, hC, Complex.re_ofReal_mul, Complex.log_re, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr h0) (norm_ne_zero_iff.mpr hψ0u'), Real.log_zpow,
          norm_inv, Real.log_inv]
        ring
      rw [cxHessian_congr heq, cxHessian_add_re (φ := fun y' => r i * Real.log ((L i).h (γ₀ y'))) C
        (contDiffAt_const.mul (pot_contDiffAt (hL i) hγ₀a hblk)) hGa]
    have hmd : maDensity (fun i y' => r i * Real.log ((L i).h (γ y'))) (Q u) =
        maDensity (fun i y' => r i * Real.log ((L i).h (γ₀ y'))) (Q u) := by
      simp only [maDensity, hH]
    rw [hmd]
    change ReciprocityTheory.AnForm.maDens _ _ = _
    have hcd : ∀ i, ContDiffAt ℝ 2 (fun v => r i * Real.log ((L i).h (lift ((A.chart j).symm v))))
        (F.symm (Q u)) := by
      intro i
      rw [hσu]
      exact contDiffAt_const.mul (pot_contDiffAt (hL i) hlift_an
        (by rw [hsu]; exact (hlift_mem x hxU).1))
    have hcomp : ReciprocityTheory.AnForm.maDens (fun i y' => r i * Real.log ((L i).h (γ₀ y'))) (Q u) =
        ReciprocityTheory.AnForm.maDens
          (fun i v => r i * Real.log ((L i).h (lift ((A.chart j).symm v))))
          (F.symm (Q u)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC F.symm (Q u)).det :=
      ReciprocityTheory.AnForm.A.maDens_comp
        (fun i v => r i * Real.log ((L i).h (lift ((A.chart j).symm v)))) F.symm (Q u) hσa hcd
    have hdetinv : LinearMap.det ((Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = (LinearMap.det (Df : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))⁻¹ := by
      have := ContinuousLinearEquiv.det_coe_symm Ce
      rw [hCe'] at this
      exact this
    rw [hcomp, hσu, ReciprocityTheory.AnForm.A.det_jacC, hσd.fderiv, hdetinv, Complex.normSq_inv,
      Complex.normSq_eq_norm_sq, div_eq_mul_inv]

theorem exists_sheet_of_resolution (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hs : IsSectionOn P A s)
    (x : R.X) (hx : x ∉ brBad R Ψ) :
    ∃ γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ, IsSheet P Ψ (brQ R Ψ x) (brW R Ψ x) γ ∧
      logNorm A s (γ (brQ R Ψ x)) * maDensity (fun j y' => pot L j (γ y')) (brQ R Ψ x) =
        logNorm A s (R.lift x x) * pushDens R.A (fun j => potOf R (L j)) (brQ R Ψ) x := by
  have hj : x ∈ (R.A.chart (chartIdx R.A x)).source := Classical.choose_spec (R.A.cover x)
  have hsu : (R.A.chart (chartIdx R.A x)).symm (R.A.chart (chartIdx R.A x) x) = x :=
    (R.A.chart (chartIdx R.A x)).left_inv hj
  have huU : R.A.chart (chartIdx R.A x) x ∈
      (R.A.chart (chartIdx R.A x)).target ∩ (R.A.chart (chartIdx R.A x)).symm ⁻¹' R.U x :=
    ⟨(R.A.chart (chartIdx R.A x)).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  obtain ⟨hQa, hQd⟩ := brGood R Ψ x hx _ hj
  obtain ⟨γ, hsh, ⟨c, hc, hγx⟩, hmd⟩ :=
    exists_sheet_of_atlas (P := P) Ψ R.A (brQ R Ψ) (R.U x) (R.lift x) L (fun _ => 1) hP hL x
      (R.isOpen_U x) (R.mem_U x) (R.mem x) hQa hQd (analyticAt_lift_chart R x _ huU)
      (analyticAt_segre_lift R Ψ x _ huU) (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx)
      (fun _ hx' => brQ_eq_local R Ψ hx')
  refine ⟨γ, hsh, ?_⟩
  obtain ⟨a, ha, hsa, -⟩ := hs
  rw [hγx, logNorm_bsmul A ha hsa hc]
  congr 1
  simp only [one_mul] at hmd
  rw [show (fun j y' => pot L j (γ y')) = (fun i y' => Real.log ((L i).h (γ y'))) from rfl, hmd]
  unfold pushDens locDens
  rw [hsu]
  rfl

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
