module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMetricPair
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergmanDensChartSum
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgePot
public import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter
  Topology Set
open scoped ContDiff ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace BlockResolutionMetricPair

section Refine

variable {e : ℕ} {X : Type} [TopologicalSpace X]

abbrev refine (A : FinHolAtlas e X) {m : ℕ} (j : Fin m → Fin A.n) (V : Fin m → Set X)
    (hV : ∀ i, IsOpen (V i)) (hcov : ∀ x, ∃ i, x ∈ (A.chart (j i)).source ∩ V i) : FinHolAtlas e X where
  n := m
  chart i := (A.chart (j i)).restrOpen (V i) (hV i)
  cover := hcov
  holo i k := (A.holo (j i) (j k)).mono fun _ hy => ⟨hy.1.1, hy.2.1⟩

variable (A : FinHolAtlas e X) {m : ℕ} (j : Fin m → Fin A.n) (V : Fin m → Set X)
    (hV : ∀ i, IsOpen (V i)) (hcov : ∀ x, ∃ i, x ∈ (A.chart (j i)).source ∩ V i)

theorem mem_refine_source {i : Fin m} {x : X} :
    x ∈ ((refine A j V hV hcov).chart i).source ↔ x ∈ (A.chart (j i)).source ∧ x ∈ V i := Iff.rfl

theorem mem_refine_target {i : Fin m} {y : Fin e → ℂ} :
    y ∈ ((refine A j V hV hcov).chart i).target ↔ y ∈ (A.chart (j i)).target ∧ (A.chart (j i)).symm y ∈ V i :=
  Iff.rfl

theorem refine_compatible : (refine A j V hV hcov).Compatible A :=
  ⟨fun i k => (A.holo (j i) k).mono fun _ hy => ⟨hy.1.1, hy.2⟩,
    fun i k => (A.holo i (j k)).mono fun _ hy => ⟨hy.1, hy.2.1⟩⟩

theorem lintegral_chart [MeasurableSpace X] [BorelSpace X] (c : OpenPartialHomeomorph X (Fin e → ℂ))
    (μ : Measure X) (ν : (Fin e → ℂ) → ℝ) (hνc : ContinuousOn ν c.target)
    (hν : ∀ S : Set X, MeasurableSet S → S ⊆ c.source →
      μ S = ∫⁻ y in c.target ∩ c.symm ⁻¹' S, ENNReal.ofReal (ν y))
    {W : Set X} (hW : IsOpen W) (g : X → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ x in c.source ∩ W, g x ∂μ = ∫⁻ y in c.target ∩ c.symm ⁻¹' W, g (c.symm y) * ENNReal.ofReal (ν y) := by
  set T := c.target ∩ c.symm ⁻¹' W with hT
  have hTm : MeasurableSet T := (c.isOpen_inter_preimage_symm hW).measurableSet
  have hsymm : AEMeasurable c.symm (volume.restrict T) :=
    (c.continuousOn_symm.mono inter_subset_left).aemeasurable hTm
  have hdens : AEMeasurable (fun y => ENNReal.ofReal (ν y)) (volume.restrict T) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hνc.mono inter_subset_left).aemeasurable hTm)
  have hsymm' : AEMeasurable c.symm ((volume.restrict T).withDensity fun y => ENNReal.ofReal (ν y)) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmeas : μ.restrict (c.source ∩ W) =
      ((volume.restrict T).withDensity fun y => ENNReal.ofReal (ν y)).map c.symm := by
    ext S hS
    rw [Measure.restrict_apply hS, Measure.map_apply_of_aemeasurable hsymm' hS, withDensity_apply',
      Measure.restrict_restrict' hTm,
      hν _ (hS.inter (c.open_source.inter hW).measurableSet) (inter_subset_right.trans inter_subset_left)]
    have hset : c.target ∩ c.symm ⁻¹' (S ∩ (c.source ∩ W)) = c.symm ⁻¹' S ∩ T := by
      ext y
      constructor
      · rintro ⟨hyt, hyS, -, hyW⟩
        exact ⟨hyS, hyt, hyW⟩
      · rintro ⟨hyS, hyt, hyW⟩
        exact ⟨hyt, hyS, c.map_target hyt, hyW⟩
    rw [hset]
  rw [hmeas, lintegral_map' hg.aemeasurable hsymm',
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun a => g (c.symm a)) hdens (hg.comp_aemeasurable hsymm)]
  refine lintegral_congr fun y => ?_
  simp [mul_comm]

end Refine

section Torus

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eval_torus {R : Type} [CommRing R] (φ : R →+* ℂ) {f : MvPolynomial (Σ k, ι k) R} {k₀ : K} {n : ℕ}
    (hf : IsMultiHomog f (blockDeg k₀ n)) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map φ f) = c k₀ ^ n * eval z (map φ f) := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hf m (support_map_subset _ _ hm)
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem prod_norm_unitDeg (c : K → ℂ) (k₀ : K) : ∏ k, ‖c k‖ ^ unitDeg k₀ k = ‖c k₀‖ := by
  rw [Fintype.prod_eq_single k₀ fun k hk => by simp [unitDeg, hk]]
  simp [unitDeg]


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

def blockRatio (k₀ : K) (z z' : (Σ k, ι k) → ℂ) : ℂ :=
  if h : ∃ i : ι k₀, z' ⟨k₀, i⟩ ≠ 0 then z ⟨k₀, h.choose⟩ / z' ⟨k₀, h.choose⟩ else 1

theorem blockRatio_eq {k₀ : K} {z' : (Σ k, ι k) → ℂ} (c : K → ℂ) (h : ∃ i : ι k₀, z' ⟨k₀, i⟩ ≠ 0) :
    blockRatio k₀ (fun p => c p.1 * z' p) z' = c k₀ := by
  rw [blockRatio, dite_eq_left h]
  exact mul_div_cancel_right₀ _ h.choose_spec

theorem blockRatio_eq_div {k₀ : K} {z z' : (Σ k, ι k) → ℂ} (hzz : SameOrbit z z') {i : ι k₀}
    (hi : z' ⟨k₀, i⟩ ≠ 0) : blockRatio k₀ z z' = z ⟨k₀, i⟩ / z' ⟨k₀, i⟩ := by
  obtain ⟨c, -, rfl⟩ := hzz
  rw [blockRatio_eq c ⟨i, hi⟩]
  exact (mul_div_cancel_right₀ _ hi).symm

theorem isConeTangent_of_map {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y)
    (hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P) (ξ : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y ξ) := by
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hpts] with w hw
    exact hw.2 f (hP0 hf)
  have hd := (adens_hasFDerivAt_eval F (γ y)).comp y hγ.differentiableAt.hasFDerivAt
  have h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero
  have := congrArg (fun L => L ξ) (hd.unique h0)
  simpa [_root_.sum_apply, smul_eq_mul] using this

theorem levi_const_mul {κ : Type} [Fintype κ] {f : (κ → ℂ) → ℝ} {z : κ → ℂ} (c : ℝ)
    (hf : ContDiffAt ℝ 2 f z) (w : κ → ℂ) : levi (fun y => c * f y) z w = c * levi f z w := by
  have h := levi_add_smul (f := fun _ => (0 : ℝ)) c contDiffAt_const hf w
  simp only [zero_add] at h
  rw [h]
  simp [levi]

end Torus

section Res

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} (R : AnRes P J D)

def nbhd (x : R.X) : Set R.X := R.U x ∩ (R.A.chart (chartIdx R.A x)).source

theorem isOpen_nbhd (x : R.X) : IsOpen (nbhd R x) := (R.isOpen_U x).inter (R.A.chart _).open_source

theorem mem_nbhd (x : R.X) : x ∈ nbhd R x := ⟨R.mem_U x, Classical.choose_spec (R.A.cover x)⟩

theorem exists_finite_nbhd_cover : ∃ (r : ℕ) (pt : Fin r → R.X), ∀ x, ∃ i, x ∈ nbhd R (pt i) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (nbhd R) (isOpen_nbhd R)
    fun x _ => mem_iUnion.2 ⟨x, mem_nbhd R x⟩
  refine ⟨t.card, fun i => (t.equivFin.symm i : R.X), fun x => ?_⟩
  obtain ⟨x', hx', hx⟩ := mem_iUnion₂.1 (ht (mem_univ x))
  exact ⟨t.equivFin ⟨x', hx'⟩, by simpa using hx⟩

variable {r : ℕ} (pt : Fin r → R.X) (hcov : ∀ x, ∃ i, x ∈ nbhd R (pt i))

abbrev atlas : FinHolAtlas D R.X :=
  refine R.A (fun i => chartIdx R.A (pt i)) (fun i => R.U (pt i)) (fun i => R.isOpen_U (pt i))
    fun x => (hcov x).imp fun _ hx => ⟨hx.2, hx.1⟩

theorem mem_atlas_source {i : Fin r} {x : R.X} (hx : x ∈ ((atlas R pt hcov).chart i).source) :
    x ∈ R.U (pt i) :=
  ((mem_refine_source _ _ _ _ _).1 hx).2

theorem mem_atlas_target {i : Fin r} {y : Fin D → ℂ} (hy : y ∈ ((atlas R pt hcov).chart i).target) :
    y ∈ (R.A.chart (chartIdx R.A (pt i))).target ∧
      ((atlas R pt hcov).chart i).symm y ∈ R.U (pt i) :=
  (mem_refine_target _ _ _ _ _).1 hy

theorem sameOrbit_lift {i k : Fin r} {x : R.X} (hi : x ∈ ((atlas R pt hcov).chart i).source)
    (hk : x ∈ ((atlas R pt hcov).chart k).source) :
    SameOrbit (R.lift (pt i) x) (R.lift (pt k) x) :=
  R.compat _ _ x ⟨mem_atlas_source R pt hcov hi, mem_atlas_source R pt hcov hk⟩

theorem lift_mem {i : Fin r} {x : R.X} (hi : x ∈ ((atlas R pt hcov).chart i).source) :
    R.lift (pt i) x ∈ mcPts P :=
  R.mem _ x (mem_atlas_source R pt hcov hi)

theorem analyticAt_lift (i k : Fin r) {y : Fin D → ℂ} (hy : y ∈ ((atlas R pt hcov).chart k).target)
    (hU : ((atlas R pt hcov).chart k).symm y ∈ R.U (pt i)) :
    AnalyticAt ℂ (fun y p => R.lift (pt i) (((atlas R pt hcov).chart k).symm y) p) y :=
  analyticAt_pi_iff.2 fun p =>
    R.holo (pt i) p (chartIdx R.A (pt k)) y ⟨(mem_atlas_target R pt hcov hy).1, hU⟩

def bundle (k₀ : K) : HolLineBundle (atlas R pt hcov) where
  g i k x := blockRatio k₀ (R.lift (pt i) x) (R.lift (pt k) x)
  holo i k := by
    intro l y hy
    have hS : IsOpen (((atlas R pt hcov).chart l).target ∩ ((atlas R pt hcov).chart l).symm ⁻¹'
        (((atlas R pt hcov).chart i).source ∩ ((atlas R pt hcov).chart k).source)) :=
      ((atlas R pt hcov).chart l).isOpen_inter_preimage_symm
        (((atlas R pt hcov).chart i).open_source.inter ((atlas R pt hcov).chart k).open_source)
    obtain ⟨hyt, hyi, hyk⟩ := hy
    obtain ⟨p, hp⟩ := (lift_mem R pt hcov hyk).1 k₀
    have f1 := analyticAt_pi_iff.1 (analyticAt_lift R pt hcov i l hyt (mem_atlas_source R pt hcov hyi))
      ⟨k₀, p⟩
    have f2 := analyticAt_pi_iff.1 (analyticAt_lift R pt hcov k l hyt (mem_atlas_source R pt hcov hyk))
      ⟨k₀, p⟩
    refine (f1.div f2 hp).congr ?_
    filter_upwards [hS.mem_nhds ⟨hyt, hyi, hyk⟩, f2.continuousAt.eventually_ne hp] with y' hy' hne
    exact (blockRatio_eq_div (sameOrbit_lift R pt hcov hy'.2.1 hy'.2.2) hne).symm
  ne_zero i k x hx := by
    obtain ⟨c, hc, hz⟩ := sameOrbit_lift R pt hcov hx.1 hx.2
    show blockRatio k₀ (R.lift (pt i) x) (R.lift (pt k) x) ≠ 0
    rw [hz, blockRatio_eq c ((lift_mem R pt hcov hx.2).1 k₀)]
    exact hc _
  cocycle i k l x hx := by
    obtain ⟨⟨hi, hk⟩, hl⟩ := hx
    obtain ⟨p, hp⟩ := (lift_mem R pt hcov hl).1 k₀
    have hkl := sameOrbit_lift R pt hcov hk hl
    have hkp : R.lift (pt k) x ⟨k₀, p⟩ ≠ 0 := by
      obtain ⟨c, hc, hz⟩ := hkl
      rw [hz]
      exact mul_ne_zero (hc _) hp
    show blockRatio k₀ (R.lift (pt i) x) (R.lift (pt l) x) =
      blockRatio k₀ (R.lift (pt i) x) (R.lift (pt k) x) * blockRatio k₀ (R.lift (pt k) x) (R.lift (pt l) x)
    rw [blockRatio_eq_div (sameOrbit_lift R pt hcov hi hl) hp,
      blockRatio_eq_div (sameOrbit_lift R pt hcov hi hk) hkp, blockRatio_eq_div hkl hp]
    field_simp

theorem contDiffAt_weight (A : HermLine ι) (hs : IsSmoothHerm A) (i l : Fin r) {y : Fin D → ℂ}
    (hy : y ∈ ((atlas R pt hcov).chart l).target) (hU : ((atlas R pt hcov).chart l).symm y ∈ R.U (pt i)) :
    ContDiffAt ℝ ∞ (fun y => 2 * Real.log (A.h (R.lift (pt i) (((atlas R pt hcov).chart l).symm y)))) y := by
  have hG := analyticAt_lift R pt hcov i l hy hU
  have hmem := R.mem (pt i) _ hU
  have hh : ContDiffAt ℝ ∞ A.h (R.lift (pt i) (((atlas R pt hcov).chart l).symm y)) :=
    hs.contDiffAt (isOpen_blockNonzero.mem_nhds hmem.1)
  have hu : ContDiffAt ℝ ∞ (fun z => 2 * Real.log (A.h z))
      (R.lift (pt i) (((atlas R pt hcov).chart l).symm y)) :=
    contDiffAt_const.mul (hh.log (A.pos _ hmem.1).ne')
  have := hu.comp y (hG.contDiffAt.restrict_scalars ℝ)
  exact this

def weight (k₀ : K) (A : HermLine ι) (hA : A.a = unitDeg k₀) (hs : IsSmoothHerm A) :
    Weight (bundle R pt hcov k₀) where
  φ i x := 2 * Real.log (A.h (R.lift (pt i) x))
  smooth i l := fun y hy =>
    (contDiffAt_weight R pt hcov A hs i l hy.1 (mem_atlas_source R pt hcov hy.2)).contDiffWithinAt
  compat i k x hx := by
    obtain ⟨c, hc, hz⟩ := sameOrbit_lift R pt hcov hx.1 hx.2
    have hk := lift_mem R pt hcov hx.2
    simp only [bundle]
    rw [hz, blockRatio_eq c (hk.1 k₀), A.smul c _ hc, hA, prod_norm_unitDeg]
    have h1 : 0 < A.h (R.lift (pt k) x) := A.pos _ hk.1
    have h2 : 0 < ‖c k₀‖ := norm_pos_iff.2 (hc _)
    rw [Real.log_mul h2.ne' h1.ne', Real.log_pow]
    push_cast
    ring

theorem weight_isSemipositive (k₀ : K) (A : HermLine ι) (hA : A.a = unitDeg k₀) (P0 : Ideal (MRing ι))
    (hP0 : P0 ≤ P) (hsp : IsSemipositiveRel P0 P A) :
    (weight R pt hcov k₀ A hA hsp.1).IsSemipositive := by
  intro l y hy w
  have hU := (mem_atlas_target R pt hcov hy).2
  have hG := analyticAt_lift R pt hcov l l hy hU
  have hmem := R.mem (pt l) _ hU
  have hh : ContDiffAt ℝ 2 A.h (R.lift (pt l) (((atlas R pt hcov).chart l).symm y)) :=
    (hsp.1.contDiffAt (isOpen_blockNonzero.mem_nhds hmem.1)).of_le (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (A.h z))
      (R.lift (pt l) (((atlas R pt hcov).chart l).symm y)) := hh.log (A.pos _ hmem.1).ne'
  have hpts : ∀ᶠ y' in 𝓝 y,
      (fun y p => R.lift (pt l) (((atlas R pt hcov).chart l).symm y) p) y' ∈ mcPts P := by
    filter_upwards [((atlas R pt hcov).chart l).open_target.mem_nhds hy] with y' hy'
    exact R.mem _ _ (mem_atlas_target R pt hcov hy').2
  have hcomp : (weight R pt hcov k₀ A hA hsp.1).φ l ∘ ((atlas R pt hcov).chart l).symm =
      (fun z => 2 * Real.log (A.h z)) ∘
        (fun y p => R.lift (pt l) (((atlas R pt hcov).chart l).symm y) p) := rfl
  rw [hcomp, levi_comp w hG (contDiffAt_const.mul hlog), levi_const_mul 2 hlog]
  exact mul_nonneg (by norm_num) (hsp.2 _ hmem _ (isConeTangent_of_map hP0 hG hpts w))

def smoothVol [MeasurableSpace R.X] [BorelSpace R.X] (dV : Measure R.X) (vol : IsSmoothVolume R.A dV) :
    SmoothVolume (atlas R pt hcov) where
  μ := dV
  isProb := vol.1
  dens i := (vol.2 (chartIdx R.A (pt i))).choose
  smooth i := (vol.2 (chartIdx R.A (pt i))).choose_spec.1.mono fun _ hy => hy.1
  pos i y hy := (vol.2 (chartIdx R.A (pt i))).choose_spec.2.1 y hy.1
  chart_lintegral i g hg :=
    lintegral_chart (R.A.chart (chartIdx R.A (pt i))) dV _ (vol.2 _).choose_spec.1.continuousOn
      (vol.2 _).choose_spec.2.2 (R.isOpen_U (pt i)) g hg

def sec {S : Type} [CommRing S] (φ : S →+* ℂ) (b : MvPolynomial (Σ k, ι k) S) :
    Fin (atlas R pt hcov).n → R.X → ℂ :=
  fun i => ((atlas R pt hcov).chart i).source.indicator
    fun x => eval (R.lift (pt i) x) (map φ b)

theorem sec_apply_of_mem {S : Type} [CommRing S] (φ : S →+* ℂ) (b : MvPolynomial (Σ k, ι k) S)
    {i : Fin r} {x : R.X} (hx : x ∈ ((atlas R pt hcov).chart i).source) :
    sec R pt hcov φ b i x = eval (R.lift (pt i) x) (map φ b) :=
  indicator_of_mem hx _

theorem sec_mem (k₀ : K) {S : Type} [CommRing S] (φ : S →+* ℂ) {n : ℕ} {b : MvPolynomial (Σ k, ι k) S}
    (hb : IsMultiHomog b (blockDeg k₀ n)) :
    sec R pt hcov φ b ∈ (bundle R pt hcov k₀).sections n := by
  refine ⟨fun i l y hy => ?_, fun i k x hx => ?_, fun i x hx => indicator_of_notMem hx _⟩
  · have hS : IsOpen (((atlas R pt hcov).chart l).target ∩ ((atlas R pt hcov).chart l).symm ⁻¹'
        ((atlas R pt hcov).chart i).source) :=
      ((atlas R pt hcov).chart l).isOpen_inter_preimage_symm ((atlas R pt hcov).chart i).open_source
    have hG := analyticAt_lift R pt hcov i l hy.1 (mem_atlas_source R pt hcov hy.2)
    refine (AnalyticAt.aeval_mvPolynomial
      (f := fun y p => R.lift (pt i) (((atlas R pt hcov).chart l).symm y) p)
      (analyticAt_pi_iff.1 hG) (map φ b)).congr ?_
    filter_upwards [hS.mem_nhds hy] with y' hy'
    have hm : ((atlas R pt hcov).chart l).symm y' ∈ ((atlas R pt hcov).chart i).source := hy'.2
    rw [Function.comp_apply, sec_apply_of_mem R pt hcov φ b hm]
    simp [aeval_def, eval]
  · obtain ⟨c, hc, hz⟩ := sameOrbit_lift R pt hcov hx.1 hx.2
    rw [sec_apply_of_mem R pt hcov φ b hx.1, sec_apply_of_mem R pt hcov φ b hx.2]
    show _ = blockRatio k₀ (R.lift (pt i) x) (R.lift (pt k) x) ^ n * _
    rw [hz, blockRatio_eq c ((lift_mem R pt hcov hx.2).1 k₀), eval_torus φ hb]

theorem lift_chartIdx (y : R.X) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      R.lift (pt (chartIdx (atlas R pt hcov) y)) y = fun p => c p.1 * R.lift y y p := by
  have hx : y ∈ ((atlas R pt hcov).chart (chartIdx (atlas R pt hcov) y)).source :=
    Classical.choose_spec ((atlas R pt hcov).cover y)
  exact R.compat _ _ y ⟨mem_atlas_source R pt hcov hx, R.mem_U y⟩

theorem locDens_eq_chernTopDens (k₀ : K) (W : Weight (bundle R pt hcov k₀))
    (Φ : LocPot R.X) (hΦ : IsPotential R.A Φ) (hU : ∀ x, Φ.U x = R.U x)
    (j : Fin r) {y : Fin D → ℂ} (hy : y ∈ ((atlas R pt hcov).chart j).target)
    (hgerm : W.φ j ∘ ((atlas R pt hcov).chart j).symm =ᶠ[𝓝 y]
      fun y' => 2 * Φ.φ (pt j) (((atlas R pt hcov).chart j).symm y')) :
    locDens (atlas R pt hcov) (fun _ => Φ) j y = chernTopDens W j y := by
  obtain ⟨hy1, hyU⟩ := mem_atlas_target R pt hcov hy
  have hL : locDens (atlas R pt hcov) (fun _ => Φ) j y =
      maDens (fun _ y' => Φ.φ (pt j) (((atlas R pt hcov).chart j).symm y')) y :=
    locDensBase R.A (fun _ => Φ) (fun _ => hΦ) (chartIdx R.A (pt j)) y hy1
      (fun _ => pt j) (fun _ => by rw [hU]; exact hyU)
  rw [hL]
  unfold chernTopDens maDens
  rw [hessCGerm _ _ y hgerm, hessC_const_mul', ReciprocityTheory.AnForm.A.mdisc_const, smul_smul, Matrix.det_smul,
    Fintype.card_fin]
  have hc : ((1 / Real.pi : ℝ) : ℂ) * ((2 : ℝ) : ℂ) = ((2 / Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hc, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  ring

theorem bergmanDens_integral_eq [MeasurableSpace R.X] [BorelSpace R.X]
    (h : BergmanDensChartSum.Statement) (k₀ : K) (dV : Measure R.X) (vol : IsSmoothVolume R.A dV)
    (W : Weight (bundle R pt hcov k₀)) (Φ : LocPot R.X) (hΦ : IsPotential R.A Φ)
    (hU : ∀ x, Φ.U x = R.U x)
    (hgerm : ∀ (j : Fin r) {y : Fin D → ℂ}, y ∈ ((atlas R pt hcov).chart j).target →
      W.φ j ∘ ((atlas R pt hcov).chart j).symm =ᶠ[𝓝 y]
        fun y' => 2 * Φ.φ (pt j) (((atlas R pt hcov).chart j).symm y'))
    (g : R.X → ℝ) (hg : Continuous g) :
    ∫ y, g y * bergmanDens W (smoothVol R pt hcov dV vol) y ∂(smoothVol R pt hcov dV vol).μ =
      mInt R.A (fun _ => Φ) g / (D.factorial : ℝ) := by
  have hΦ' : ∀ _ : Fin D, IsPotential R.A Φ := fun _ => hΦ
  have hMI := mIntegrableCont R.A _ hΦ' g hg
  have hcomp := refine_compatible R.A (fun i => chartIdx R.A (pt i)) (fun i => R.U (pt i))
    (fun i => R.isOpen_U (pt i)) fun x => (hcov x).imp fun _ hx => ⟨hx.2, hx.1⟩
  have hcompat : R.A.Compatible (atlas R pt hcov) := ⟨hcomp.2, hcomp.1⟩
  have hIndep : mInt R.A (fun _ => Φ) g = mInt (atlas R pt hcov) (fun _ => Φ) g := by
    have hU' := compatible_unionAtlas_left R.A (atlas R pt hcov) hcompat
    have hPU := fun i => isPotential_of_compatible hU' (hΦ' i)
    have hgU := mIntegrable_of_compatible hU' _ hΦ' hMI
    have hP' := fun i => isPotential_of_compatible hcompat (hΦ' i)
    have hg' := mIntegrable_of_compatible hcompat _ hΦ' hMI
    obtain ⟨P₁⟩ := existsPartition R.A
    obtain ⟨P₂⟩ := existsPartition (atlas R pt hcov)
    rw [mIntEq R.A P₁ _ hΦ' g hMI, mIntEq (atlas R pt hcov) P₂ _ hP' g hg',
      ← integralWith_extendLeft hcompat P₁ _ g, ← integralWith_extendRight hcompat P₂ _ g]
    exact integralWithIndep _ _ _ _ hPU g hgU
  rw [hIndep]
  have hP : Nonempty (ChartPartition (atlas R pt hcov)) := existsPartition _
  rw [h (atlas R pt hcov) (bundle R pt hcov k₀) W (smoothVol R pt hcov dV vol) hP.some g hg]
  unfold mInt
  rw [dite_eq_left hP]
  unfold integralWith
  congr 1
  refine Finset.sum_congr rfl fun j _ => setIntegral_congr_fun
    (((atlas R pt hcov).chart j).open_target.measurableSet) fun y hy => ?_
  simp only
  rw [locDens_eq_chernTopDens R pt hcov k₀ W Φ hΦ hU j hy (hgerm j hy)]

end Res

theorem isPotential_blockInterpPot {D : ℕ} {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
    (d : HSMBlockDatum D K ι Ω) {A' : HermLine ι} (hA' : IsSmoothHerm A') (t : ℝ) :
    IsPotential d.R.A (blockInterpPot d d.A A' t) := by
  have h₀ := isPotentialRsmul d.R.A (1 - t) _ (AnResBridge.isPotential_potOf d.R d.semipos.1)
  have h₁ := isPotentialRsmul d.R.A t _ (AnResBridge.isPotential_potOf d.R hA')
  have hs := isPotentialAdd d.R.A _ _ h₀ h₁
  refine isPotential_mul d.R.A _ hs 1 _ ?_ fun x y => ?_
  · funext x
    exact (Set.inter_self _).symm
  · show _ = 1 * ((1 - t) * Real.log (d.A.h (d.R.lift x y)) + t * Real.log (A'.h (d.R.lift x y)))
    simp [blockInterpPot]

end BlockResolutionMetricPair


open BlockResolutionMetricPair in
theorem BlockResolutionMetricPair.proof (h : BergmanDensChartSum.Statement) : BlockResolutionMetricPair.Statement := by
  intro D K _ _ ι _ Ω _ _ d A' P0' hA' hP0' hsp'
  obtain ⟨r, pt, hcov⟩ := exists_finite_nbhd_cover d.R
  refine ⟨atlas d.R pt hcov, bundle d.R pt hcov d.k₀, weight d.R pt hcov d.k₀ d.A d.deg d.semipos.1,
    weight d.R pt hcov d.k₀ A' hA' hsp'.1, smoothVol d.R pt hcov d.dV d.vol,
    fun _ b => sec d.R pt hcov (algebraMap ℚ ℂ) b, refine_compatible _ _ _ _ _,
    weight_isSemipositive d.R pt hcov d.k₀ d.A d.deg d.P0 d.normalForm_baseLattice_le_dualSpan_sup_line d.semipos,
    weight_isSemipositive d.R pt hcov d.k₀ A' hA' P0' hP0' hsp', rfl,
    fun n b hb => sec_mem d.R pt hcov d.k₀ (algebraMap ℚ ℂ) hb, fun y => ?_, fun s _ g hg => ?_⟩
  · obtain ⟨c, hc, hz⟩ := lift_chartIdx d.R pt hcov y
    have hx : y ∈ ((atlas d.R pt hcov).chart (chartIdx (atlas d.R pt hcov) y)).source :=
      Classical.choose_spec ((atlas d.R pt hcov).cover y)
    refine ⟨c, hc, fun n b _ => ?_, ?_, ?_⟩
    · show sec d.R pt hcov (algebraMap ℚ ℂ) b (chartIdx (atlas d.R pt hcov) y) y = _
      rw [sec_apply_of_mem d.R pt hcov (algebraMap ℚ ℂ) b hx, hz]; rfl
    · show 2 * Real.log (d.A.h (d.R.lift (pt _) y)) = _
      rw [hz]; rfl
    · show 2 * Real.log (A'.h (d.R.lift (pt _) y)) = _
      rw [hz]; rfl
  · refine bergmanDens_integral_eq d.R pt hcov h d.k₀ d.dV d.vol _ (blockInterpPot d d.A A' s)
      (isPotential_blockInterpPot d hsp'.1 s) (fun _ => rfl) (fun j _ _ => ?_) g hg
    refine Filter.Eventually.of_forall fun y' => ?_
    simp only [Function.comp_apply, Weight.lerp, weight, blockInterpPot]
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
