module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.RingTheory.Complex
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

namespace GroundTheory.Automorphic

open MeasureTheory Matrix Measure
open scoped Matrix.Norms.L2Operator ENNReal Kronecker

section Det

variable {𝕜 : Type*} [Field 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

def vecLinearEquiv : Matrix n n 𝕜 ≃ₗ[𝕜] (n × n → 𝕜) where
  toFun := vec
  invFun v := of fun i j => v (j, i)
  map_add' := vec_add
  map_smul' := vec_smul
  left_inv _ := rfl
  right_inv _ := funext fun _ => rfl

theorem det_mulLeft_matrix (A : Matrix n n 𝕜) :
    LinearMap.det (LinearMap.mulLeft 𝕜 A) = A.det ^ Fintype.card n := by
  have h : (vecLinearEquiv : Matrix n n 𝕜 ≃ₗ[𝕜] (n × n → 𝕜)).toLinearMap ∘ₗ
      LinearMap.mulLeft 𝕜 A ∘ₗ (vecLinearEquiv (n := n)).symm.toLinearMap = toLin' (1 ⊗ₖ A) := by
    apply LinearMap.ext; intro v
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.mulLeft_apply, toLin'_apply]
    show vec (A * vecLinearEquiv.symm v) = _
    rw [vec_mul_eq_mulVec]
    rfl
  rw [← LinearMap.det_conj (LinearMap.mulLeft 𝕜 A) vecLinearEquiv, h, LinearMap.det_toLin',
    det_kronecker, det_one, one_pow, one_mul]

theorem det_mulRight_matrix (A : Matrix n n 𝕜) :
    LinearMap.det (LinearMap.mulRight 𝕜 A) = A.det ^ Fintype.card n := by
  have h : (vecLinearEquiv : Matrix n n 𝕜 ≃ₗ[𝕜] (n × n → 𝕜)).toLinearMap ∘ₗ
      LinearMap.mulRight 𝕜 A ∘ₗ (vecLinearEquiv (n := n)).symm.toLinearMap =
        toLin' (A ⊗ₖ (1 : Matrix n n 𝕜))ᵀ := by
    apply LinearMap.ext; intro v
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.mulRight_apply, toLin'_apply]
    show vec (vecLinearEquiv.symm v * A) = _
    rw [vec_mul_eq_vecMul, mulVec_transpose]
    rfl
  rw [← LinearMap.det_conj (LinearMap.mulRight 𝕜 A) vecLinearEquiv, h, LinearMap.det_toLin',
    det_transpose, det_kronecker, det_one, one_pow, mul_one]

end Det

section General

theorem map_withDensity_eq_of_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ₀ : Measure E)
    {ρ : E → ℝ≥0∞} (hρ : Measurable ρ) (L : E →ₗ[ℝ] E) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcT : c ≠ ∞)
    (hmap : Measure.map L μ₀ = c • μ₀) (hρL : ∀ x, ρ (L x) = c * ρ x) :
    Measure.map L (μ₀.withDensity ρ) = μ₀.withDensity ρ := by
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  ext s hs
  rw [Measure.map_apply hLm hs, withDensity_apply _ (hLm hs), withDensity_apply _ hs]
  have key : ∫⁻ y, s.indicator ρ y ∂(Measure.map L μ₀) = ∫⁻ x, s.indicator ρ (L x) ∂μ₀ :=
    lintegral_map (hρ.indicator hs) hLm
  rw [hmap, lintegral_smul_measure, lintegral_indicator hs] at key
  have h2 : (fun x => s.indicator ρ (L x)) = fun x => c * (L ⁻¹' s).indicator ρ x := by
    funext x
    by_cases hx : L x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ L ⁻¹' s from hx), hρL]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ L ⁻¹' s from hx),
        mul_zero]
  rw [h2, lintegral_const_mul _ (hρ.indicator (hLm hs)), lintegral_indicator (hLm hs)] at key
  exact ((ENNReal.mul_right_inj hc0 hcT).1 key).symm

theorem image_val_preimage_mul_left {M : Type*} [Monoid M] (g : Mˣ) (s : Set Mˣ) :
    Units.val '' ((fun h => g * h) ⁻¹' s) = (fun x : M => (g : M) * x) ⁻¹' (Units.val '' s) := by
  ext x
  constructor
  · rintro ⟨h, hs, rfl⟩; exact ⟨g * h, hs, rfl⟩
  · rintro ⟨h', hs, hx⟩
    refine ⟨g⁻¹ * h', by simpa using hs, ?_⟩
    rw [Units.val_mul, hx, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem image_val_preimage_mul_right {M : Type*} [Monoid M] (g : Mˣ) (s : Set Mˣ) :
    Units.val '' ((fun h => h * g) ⁻¹' s) = (fun x : M => x * (g : M)) ⁻¹' (Units.val '' s) := by
  ext x
  constructor
  · rintro ⟨h, hs, rfl⟩; exact ⟨h * g, hs, rfl⟩
  · rintro ⟨h', hs, hx⟩
    refine ⟨h' * g⁻¹, by simpa using hs, ?_⟩
    rw [Units.val_mul, hx, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

end General

section RCLikeHaar

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

private noncomputable def haarDensityGL (d : ℕ) (x : Matrix n n 𝕜) : ℝ≥0∞ :=
  ENNReal.ofReal ((‖x.det‖ ^ d)⁻¹ ^ Fintype.card n)

private theorem measurable_haarDensityGL [MeasurableSpace (Matrix n n 𝕜)]
    [BorelSpace (Matrix n n 𝕜)] (d : ℕ) :
    Measurable (haarDensityGL (𝕜 := 𝕜) (n := n) d) :=
  ENNReal.measurable_ofReal.comp
    ((((continuous_id.matrix_det).norm.pow _).measurable.inv).pow_const _)

private theorem haarDensityGL_mul (d : ℕ) (A x : Matrix n n 𝕜) :
    haarDensityGL d (A * x) = ENNReal.ofReal ((‖A.det‖ ^ d)⁻¹ ^ Fintype.card n) *
      haarDensityGL d x := by
  simp only [haarDensityGL, det_mul, norm_mul, mul_pow, mul_inv]
  rw [ENNReal.ofReal_mul (by positivity)]

private theorem haarDensityGL_mul' (d : ℕ) (A x : Matrix n n 𝕜) :
    haarDensityGL d (x * A) = ENNReal.ofReal ((‖A.det‖ ^ d)⁻¹ ^ Fintype.card n) *
      haarDensityGL d x := by
  rw [← haarDensityGL_mul]
  simp only [haarDensityGL, det_mul, mul_comm]

private theorem haarScale_ne_zero (d : ℕ) (g : GL n 𝕜) :
    ENNReal.ofReal ((‖(g : Matrix n n 𝕜).det‖ ^ d)⁻¹ ^ Fintype.card n) ≠ 0 := by
  have hd : (g : Matrix n n 𝕜).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  exact (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 (pow_pos (norm_pos_iff.2 hd) _)) _)).ne'

private theorem map_linearMap_haar_eq {d : ℕ} [MeasurableSpace (Matrix n n 𝕜)]
    [BorelSpace (Matrix n n 𝕜)]
    (μ₀ : Measure (Matrix n n 𝕜)) [μ₀.IsAddHaarMeasure]
    (g : GL n 𝕜) (L : Matrix n n 𝕜 →ₗ[ℝ] Matrix n n 𝕜)
    (hdet : |LinearMap.det L| = (‖(g : Matrix n n 𝕜).det‖ ^ d) ^ Fintype.card n) :
    Measure.map L μ₀ = ENNReal.ofReal ((‖(g : Matrix n n 𝕜).det‖ ^ d)⁻¹ ^ Fintype.card n) • μ₀ := by
  let : NormedSpace ℝ (Matrix n n 𝕜) :=
    { norm_smul_le := fun r x => by
        rw [← algebraMap_smul 𝕜 r x, norm_smul, norm_algebraMap'] }
  have hd : (g : Matrix n n 𝕜).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  have hL : LinearMap.det L ≠ 0 := by
    rw [← abs_ne_zero, hdet]
    exact pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 hd))
  rw [map_linearMap_addHaar_eq_smul_addHaar μ₀ hL, abs_inv, hdet, inv_pow]

private noncomputable def haarGL [MeasurableSpace (Matrix n n 𝕜)]
    (d : ℕ) (μ₀ : Measure (Matrix n n 𝕜)) : Measure (GL n 𝕜) :=
  Measure.comap Units.val (μ₀.withDensity (haarDensityGL d))

private theorem borelSpace_GL [MeasurableSpace (Matrix n n 𝕜)] [BorelSpace (Matrix n n 𝕜)] :
    BorelSpace (GL n 𝕜) :=
  ⟨by
    change MeasurableSpace.comap Units.val ‹MeasurableSpace (Matrix n n 𝕜)› = borel (GL n 𝕜)
    rw [BorelSpace.measurable_eq (α := Matrix n n 𝕜),
      Units.isOpenEmbedding_val.isEmbedding.eq_induced, borel_comap]⟩

private theorem haarGL_apply [MeasurableSpace (Matrix n n 𝕜)] [BorelSpace (Matrix n n 𝕜)] (d : ℕ)
    (μ₀ : Measure (Matrix n n 𝕜)) (s : Set (GL n 𝕜)) :
    haarGL d μ₀ s = μ₀.withDensity (haarDensityGL d) (Units.val '' s) := by
  have : BorelSpace (GL n 𝕜) := borelSpace_GL
  exact Units.isOpenEmbedding_val.measurableEmbedding.comap_apply _ s

private theorem map_mul_haarGL_eq_self {d : ℕ} [MeasurableSpace (Matrix n n 𝕜)]
    [BorelSpace (Matrix n n 𝕜)] (μ₀ : Measure (Matrix n n 𝕜))
    {f : GL n 𝕜 → GL n 𝕜} (hf : Continuous f)
    (L : Matrix n n 𝕜 →ₗ[ℝ] Matrix n n 𝕜) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcT : c ≠ ∞)
    (him : ∀ s : Set (GL n 𝕜), Units.val '' (f ⁻¹' s) = L ⁻¹' (Units.val '' s))
    (hmap : Measure.map L μ₀ = c • μ₀)
    (hρ : ∀ x, haarDensityGL d (L x) = c * haarDensityGL d x) :
    Measure.map f (haarGL d μ₀) = haarGL d μ₀ := by
  let : NormedSpace ℝ (Matrix n n 𝕜) :=
    { norm_smul_le := fun r x => by
        rw [← algebraMap_smul 𝕜 r x, norm_smul, norm_algebraMap'] }
  have : BorelSpace (GL n 𝕜) := borelSpace_GL
  ext s hs
  rw [Measure.map_apply hf.measurable hs, haarGL_apply, haarGL_apply, him]
  have hmeas : MeasurableSet (Units.val '' s) :=
    Units.isOpenEmbedding_val.measurableEmbedding.measurableSet_image.2 hs
  have h := congrArg (fun m : Measure (Matrix n n 𝕜) => m (Units.val '' s))
    (map_withDensity_eq_of_scale μ₀ (measurable_haarDensityGL d) L hc0 hcT hmap hρ)
  rwa [Measure.map_apply L.continuous_of_finiteDimensional.measurable hmeas] at h

private theorem isHaarMeasure_haarGL (d : ℕ) [MeasurableSpace (Matrix n n 𝕜)]
    [BorelSpace (Matrix n n 𝕜)] (μ₀ : Measure (Matrix n n 𝕜))
    [μ₀.IsAddHaarMeasure] (hleft : (haarGL d μ₀).IsMulLeftInvariant) :
    (haarGL d μ₀).IsHaarMeasure where
  lt_top_of_isCompact := fun K hK => by
    have : BorelSpace (GL n 𝕜) := borelSpace_GL
    rw [haarGL_apply]
    have hK' : IsCompact (Units.val '' K) := hK.image Units.continuous_val
    have hmeas : MeasurableSet (Units.val '' K) := hK'.isClosed.measurableSet
    have hcont : Continuous (fun h : GL n 𝕜 =>
        (‖(h : Matrix n n 𝕜).det‖ ^ d)⁻¹ ^ Fintype.card n) :=
      (((Units.continuous_val.matrix_det).norm.pow _).inv₀ (fun h => pow_ne_zero _
        (norm_ne_zero_iff.2 ((isUnit_iff_isUnit_det _).1 h.isUnit).ne_zero))).pow _
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
    rw [withDensity_apply _ hmeas]
    calc ∫⁻ x in Units.val '' K, haarDensityGL d x ∂μ₀
        ≤ ∫⁻ _ in Units.val '' K, ENNReal.ofReal C ∂μ₀ := by
          refine setLIntegral_mono' hmeas fun x hx => ?_
          obtain ⟨h, hK, rfl⟩ := hx
          refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
          simpa [Real.norm_eq_abs] using hC h hK
      _ = ENNReal.ofReal C * μ₀ (Units.val '' K) := setLIntegral_const _ _
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK'.measure_lt_top
  map_mul_left_eq_self := hleft.map_mul_left_eq_self
  open_pos := fun U hU hne => by
    have : BorelSpace (GL n 𝕜) := borelSpace_GL
    rw [haarGL_apply, ne_eq,
      withDensity_apply_eq_zero' (measurable_haarDensityGL d).aemeasurable]
    have e : {x | haarDensityGL d x ≠ 0} ∩ Units.val '' U = Units.val '' U := by
      refine Set.inter_eq_right.2 ?_
      rintro _ ⟨h, _, rfl⟩
      exact haarScale_ne_zero d h
    rw [e]
    exact (Units.isOpenEmbedding_val.isOpenMap U hU).measure_ne_zero μ₀ (hne.image _)

end RCLikeHaar

section Real

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable scoped instance matrixMeasurableSpaceReal : MeasurableSpace (Matrix n n ℝ) := borel _

scoped instance matrixBorelSpaceReal : BorelSpace (Matrix n n ℝ) := ⟨rfl⟩

instance borelSpace_GLReal : BorelSpace (GL n ℝ) := borelSpace_GL

noncomputable def haarDensityGLReal (x : Matrix n n ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((‖x.det‖ ^ 1)⁻¹ ^ Fintype.card n)

theorem haarDensityGLReal_mul (A x : Matrix n n ℝ) :
    haarDensityGLReal (A * x) = ENNReal.ofReal ((‖A.det‖ ^ 1)⁻¹ ^ Fintype.card n) *
      haarDensityGLReal x :=
  haarDensityGL_mul 1 A x

theorem haarDensityGLReal_mul' (A x : Matrix n n ℝ) :
    haarDensityGLReal (x * A) = ENNReal.ofReal ((‖A.det‖ ^ 1)⁻¹ ^ Fintype.card n) *
      haarDensityGLReal x :=
  haarDensityGL_mul' 1 A x

theorem map_mulLeft_haarReal (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure] (g : GL n ℝ) :
    Measure.map (LinearMap.mulLeft ℝ (g : Matrix n n ℝ)) μ₀ =
      ENNReal.ofReal ((‖(g : Matrix n n ℝ).det‖ ^ 1)⁻¹ ^ Fintype.card n) • μ₀ :=
  map_linearMap_haar_eq μ₀ g _ (by
    rw [det_mulLeft_matrix, abs_pow, Real.norm_eq_abs, pow_one])

theorem map_mulRight_haarReal (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure] (g : GL n ℝ) :
    Measure.map (LinearMap.mulRight ℝ (g : Matrix n n ℝ)) μ₀ =
      ENNReal.ofReal ((‖(g : Matrix n n ℝ).det‖ ^ 1)⁻¹ ^ Fintype.card n) • μ₀ :=
  map_linearMap_haar_eq μ₀ g _ (by
    rw [det_mulRight_matrix, abs_pow, Real.norm_eq_abs, pow_one])

noncomputable def haarGLReal (μ₀ : Measure (Matrix n n ℝ)) : Measure (GL n ℝ) :=
  Measure.comap Units.val (μ₀.withDensity haarDensityGLReal)

theorem haarScaleReal_ne_zero (g : GL n ℝ) :
    ENNReal.ofReal ((‖(g : Matrix n n ℝ).det‖ ^ 1)⁻¹ ^ Fintype.card n) ≠ 0 :=
  haarScale_ne_zero 1 g

instance isMulLeftInvariant_haarGLReal (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure] :
    (haarGLReal μ₀).IsMulLeftInvariant :=
  ⟨fun g => map_mul_haarGL_eq_self μ₀ (continuous_const.mul continuous_id)
    (LinearMap.mulLeft ℝ (g : Matrix n n ℝ)) (haarScaleReal_ne_zero g) ENNReal.ofReal_ne_top
    (image_val_preimage_mul_left g) (map_mulLeft_haarReal μ₀ g) (haarDensityGLReal_mul _)⟩

instance isMulRightInvariant_haarGLReal (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure] :
    (haarGLReal μ₀).IsMulRightInvariant :=
  ⟨fun g => map_mul_haarGL_eq_self μ₀ (continuous_id.mul continuous_const)
    (LinearMap.mulRight ℝ (g : Matrix n n ℝ)) (haarScaleReal_ne_zero g) ENNReal.ofReal_ne_top
    (image_val_preimage_mul_right g) (map_mulRight_haarReal μ₀ g) (haarDensityGLReal_mul' _)⟩

instance isHaarMeasure_haarGLReal (μ₀ : Measure (Matrix n n ℝ)) [μ₀.IsAddHaarMeasure] :
    (haarGLReal μ₀).IsHaarMeasure :=
  isHaarMeasure_haarGL 1 μ₀ (isMulLeftInvariant_haarGLReal μ₀)

end Real

section Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable scoped instance matrixMeasurableSpaceComplex : MeasurableSpace (Matrix n n ℂ) := borel _

scoped instance matrixBorelSpaceComplex : BorelSpace (Matrix n n ℂ) := ⟨rfl⟩

instance borelSpace_GLComplex : BorelSpace (GL n ℂ) := borelSpace_GL

noncomputable def haarDensityGLComplex (x : Matrix n n ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((‖x.det‖ ^ 2)⁻¹ ^ Fintype.card n)

theorem measurable_haarDensityGLComplex : Measurable (haarDensityGLComplex (n := n)) :=
  measurable_haarDensityGL 2

theorem haarDensityGLComplex_mul (A x : Matrix n n ℂ) :
    haarDensityGLComplex (A * x) = ENNReal.ofReal ((‖A.det‖ ^ 2)⁻¹ ^ Fintype.card n) *
      haarDensityGLComplex x :=
  haarDensityGL_mul 2 A x

theorem haarDensityGLComplex_mul' (A x : Matrix n n ℂ) :
    haarDensityGLComplex (x * A) = ENNReal.ofReal ((‖A.det‖ ^ 2)⁻¹ ^ Fintype.card n) *
      haarDensityGLComplex x :=
  haarDensityGL_mul' 2 A x

theorem det_restrictScalars_mulLeft (A : Matrix n n ℂ) :
    LinearMap.det ((LinearMap.mulLeft ℂ A).restrictScalars ℝ) = (‖A.det‖ ^ 2) ^ Fintype.card n := by
  rw [LinearMap.det_restrictScalars, det_mulLeft_matrix, map_pow, Algebra.norm_complex_eq]
  simp [Complex.normSq_eq_norm_sq]

theorem det_restrictScalars_mulRight (A : Matrix n n ℂ) :
    LinearMap.det ((LinearMap.mulRight ℂ A).restrictScalars ℝ) = (‖A.det‖ ^ 2) ^ Fintype.card n := by
  rw [LinearMap.det_restrictScalars, det_mulRight_matrix, map_pow, Algebra.norm_complex_eq]
  simp [Complex.normSq_eq_norm_sq]

theorem map_mulLeft_haarComplex (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure] (g : GL n ℂ) :
    Measure.map ((LinearMap.mulLeft ℂ (g : Matrix n n ℂ)).restrictScalars ℝ) μ₀ =
      ENNReal.ofReal ((‖(g : Matrix n n ℂ).det‖ ^ 2)⁻¹ ^ Fintype.card n) • μ₀ :=
  map_linearMap_haar_eq μ₀ g _ (by
    rw [det_restrictScalars_mulLeft, abs_of_nonneg (by positivity)])

theorem map_mulRight_haarComplex (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure] (g : GL n ℂ) :
    Measure.map ((LinearMap.mulRight ℂ (g : Matrix n n ℂ)).restrictScalars ℝ) μ₀ =
      ENNReal.ofReal ((‖(g : Matrix n n ℂ).det‖ ^ 2)⁻¹ ^ Fintype.card n) • μ₀ :=
  map_linearMap_haar_eq μ₀ g _ (by
    rw [det_restrictScalars_mulRight, abs_of_nonneg (by positivity)])

noncomputable def haarGLComplex (μ₀ : Measure (Matrix n n ℂ)) : Measure (GL n ℂ) :=
  Measure.comap Units.val (μ₀.withDensity haarDensityGLComplex)

theorem measurableEmbedding_val_GLComplex :
    MeasurableEmbedding (Units.val : GL n ℂ → Matrix n n ℂ) :=
  Units.isOpenEmbedding_val.measurableEmbedding

theorem haarGLComplex_apply (μ₀ : Measure (Matrix n n ℂ)) (s : Set (GL n ℂ)) :
    haarGLComplex μ₀ s = μ₀.withDensity haarDensityGLComplex (Units.val '' s) :=
  haarGL_apply 2 μ₀ s

theorem haarScaleComplex_ne_zero (g : GL n ℂ) :
    ENNReal.ofReal ((‖(g : Matrix n n ℂ).det‖ ^ 2)⁻¹ ^ Fintype.card n) ≠ 0 :=
  haarScale_ne_zero 2 g

instance isMulLeftInvariant_haarGLComplex (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure] :
    (haarGLComplex μ₀).IsMulLeftInvariant :=
  ⟨fun g => map_mul_haarGL_eq_self μ₀ (continuous_const.mul continuous_id)
    ((LinearMap.mulLeft ℂ (g : Matrix n n ℂ)).restrictScalars ℝ) (haarScaleComplex_ne_zero g)
    ENNReal.ofReal_ne_top (image_val_preimage_mul_left g) (map_mulLeft_haarComplex μ₀ g)
    (haarDensityGLComplex_mul _)⟩

instance isMulRightInvariant_haarGLComplex (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure] :
    (haarGLComplex μ₀).IsMulRightInvariant :=
  ⟨fun g => map_mul_haarGL_eq_self μ₀ (continuous_id.mul continuous_const)
    ((LinearMap.mulRight ℂ (g : Matrix n n ℂ)).restrictScalars ℝ) (haarScaleComplex_ne_zero g)
    ENNReal.ofReal_ne_top (image_val_preimage_mul_right g) (map_mulRight_haarComplex μ₀ g)
    (haarDensityGLComplex_mul' _)⟩

instance isHaarMeasure_haarGLComplex (μ₀ : Measure (Matrix n n ℂ)) [μ₀.IsAddHaarMeasure] :
    (haarGLComplex μ₀).IsHaarMeasure :=
  isHaarMeasure_haarGL 2 μ₀ (isMulLeftInvariant_haarGLComplex μ₀)

end Complex

end GroundTheory.Automorphic
