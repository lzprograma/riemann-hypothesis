module

public import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoBasic
public import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoCutoff
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoStep
import Mathlib.Tactic.TypeStar
import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoCalc
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoGarding, GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoSeries, GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoelliptic

-- ===== clump member: GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoGarding =====
-- clump-header: {"m": "GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoGarding", "h": "module\n\npublic import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoBasic\npublic import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoCutoff\npublic import Mathlib.Analysis.Real.Pi.Bounds\n\n"}
section -- clump:auto
@[expose] public section
namespace GroundTheory.Automorphic.Sobolev
open MeasureTheory SchwartzMap LineDeriv FourierTransform Real
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem fourier_iteratedLineDerivOp_apply (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) {k : ℕ}
    (w : Fin k → EuclideanSpace ℝ (Fin n)) (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (∂^{w} f) ξ = (∏ l, (2 * π * Complex.I) * (inner ℝ ξ (w l) : ℂ)) * 𝓕 f ξ := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    have hg : (fun x : EuclideanSpace ℝ (Fin n) ↦ inner ℝ x (w 0)).HasTemperateGrowth :=
      ((innerSL ℝ).flip (w 0)).hasTemperateGrowth
    rw [iteratedLineDerivOp_succ_left, fourier_lineDerivOp_eq, smul_apply,
      smulLeftCLM_apply_apply hg, ih, Fin.prod_univ_succ]
    simp only [Fin.tail, Complex.real_smul, smul_eq_mul]; ring

section Plancherel
variable {v : EuclideanSpace ℝ (Fin n) → ℂ}
theorem pdT_eq_iteratedLineDerivOp (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) {k : ℕ}
    (J : Fin k → Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    pdT J v x = (∂^{fun l ↦ ev (J l)} (hvc.toSchwartzMap hv)) x := by
  rw [iteratedLineDerivOp_eq_iteratedFDeriv]; rfl
theorem integrable_norm_sq_schwartz (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Integrable (fun x ↦ ‖g x‖ ^ 2) := by
  simpa using (g.memLp 2).integrable_norm_pow (p := 2) two_ne_zero
theorem norm_sq_fourier_pdT (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) {k : ℕ} (J : Fin k → Fin n)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖𝓕 (∂^{fun l ↦ ev (J l)} φ) ξ‖ ^ 2 = (∏ l, (2 * π) ^ 2 * ξ (J l) ^ 2) * ‖𝓕 φ ξ‖ ^ 2 := by
  rw [fourier_iteratedLineDerivOp_apply, norm_mul, norm_prod, mul_pow, ← Finset.prod_pow]; congr 1
  exact Finset.prod_congr rfl fun l _ ↦ by
    simp [ev, EuclideanSpace.inner_single_right, mul_pow, abs_of_pos Real.pi_pos, sq_abs]
private theorem sum_norm_sq_fourier_pdT (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (q : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    ∑ J : Fin q → Fin n,
      ‖(𝓕 (∂^{fun l ↦ ev (J l)} (hvc.toSchwartzMap hv)) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ξ‖ ^ 2 =
      ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ q * ‖𝓕 v ξ‖ ^ 2 := by
  simp_rw [norm_sq_fourier_pdT, ← Finset.sum_mul, congrFun (fourier_coe _) ξ]; congr 1
  have h := Finset.prod_univ_sum (fun _ : Fin q ↦ (Finset.univ : Finset (Fin n)))
    fun _ i ↦ (2 * π) ^ 2 * ξ i ^ 2
  rw [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← h, ← Finset.mul_sum, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]; simp
theorem integral_hsD_sq (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (q : ℕ) :
    ∫ x, hsD q v x ^ 2 = ∫ ξ, ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ q * ‖𝓕 v ξ‖ ^ 2 := by
  simp_rw [hsD_sq, pdT_eq_iteratedLineDerivOp hv hvc]
  rw [integral_finsetSum _ fun _ _ ↦ integrable_norm_sq_schwartz _,
    Finset.sum_congr rfl fun _ _ ↦ (integral_norm_sq_fourier _).symm,
    ← integral_finsetSum _ fun _ _ ↦ integrable_norm_sq_schwartz _]
  exact integral_congr_ae (ae_of_all _ (sum_norm_sq_fourier_pdT hv hvc q))
end Plancherel

section Symbol
variable {m : ℕ} {A : Finset (Fin n → ℕ)} {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}
def frozenOp (A : Finset (Fin n → ℕ)) (a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ) (m : ℕ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑ α ∈ A with mabs α = m, a α x₀ * pderiv α v x
theorem fourier_mdir_apply (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (α : Fin n → ℕ)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (∂^{mdir α} φ) ξ = (2 * π * Complex.I) ^ mabs α * (mpow α ξ : ℂ) * 𝓕 φ ξ := by
  rw [fourier_iteratedLineDerivOp_apply, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← prod_inner_mdir α ξ]; push_cast; ring
theorem prinSymbol_smul (x₀ ξ : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    prinSymbol A a m x₀ (t • ξ) = (t : ℂ) ^ m * prinSymbol A a m x₀ ξ := by
  rw [prinSymbol, prinSymbol, Finset.mul_sum]; refine Finset.sum_congr rfl fun α hα ↦ ?_
  have h : mpow α (t • ξ) = t ^ m * mpow α ξ := by
    simp only [mpow, PiLp.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, show ∑ i, α i = m from (Finset.mem_filter.1 hα).2]
  rw [h]; push_cast; ring
theorem continuous_prinSymbol (x₀ : EuclideanSpace ℝ (Fin n)) :
    Continuous (prinSymbol A a m x₀) := by unfold prinSymbol mpow; fun_prop
theorem exists_prinSymbol_lower_bound (hnm : 0 < n ∨ 1 ≤ m) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hell : ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A a m x₀ ξ ≠ 0) :
    ∃ c > 0, ∀ ξ : EuclideanSpace ℝ (Fin n), c * ‖ξ‖ ^ m ≤ ‖prinSymbol A a m x₀ ξ‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_pos, fun ξ ↦ ?_⟩
    rw [Subsingleton.elim ξ 0, norm_zero, zero_pow (by omega), mul_zero]; exact norm_nonneg _
  obtain ⟨u₀, hu₀S, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMinOn
    ⟨ev ⟨0, hn⟩, by simp [norm_ev]⟩ (continuous_prinSymbol x₀).norm.continuousOn
  refine ⟨‖prinSymbol A a m x₀ u₀‖, norm_pos_iff.2 (hell u₀ (by rintro rfl; simp at hu₀S)), fun ξ ↦ ?_⟩
  obtain ⟨u, huS, hξu⟩ : ∃ u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ξ = ‖ξ‖ • u :=
    if hξ : ξ = 0 then ⟨u₀, hu₀S, by simp [hξ]⟩ else
      ⟨‖ξ‖⁻¹ • ξ, by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hξ)],
        by rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hξ), one_smul]⟩
  conv_rhs => rw [hξu]
  rw [prinSymbol_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), mul_comm]
  exact mul_le_mul_of_nonneg_left (hmin huS) (by positivity)
theorem exists_schwartz_frozenOp {v : EuclideanSpace ℝ (Fin n) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ x, ψ x = frozenOp A a m x₀ v x) ∧
      ∀ ξ, ‖(𝓕 ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ξ‖ ^ 2 =
        (2 * π) ^ (2 * m) * ‖prinSymbol A a m x₀ ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2 := by
  set φ := hvc.toSchwartzMap hv
  refine ⟨∑ α ∈ A with mabs α = m, a α x₀ • ∂^{mdir α} φ, fun _ ↦ by
    simp only [frozenOp, sum_apply, smul_apply, smul_eq_mul, iteratedLineDerivOp_eq_iteratedFDeriv]
    rfl, fun ξ ↦ (congrArg (fun z : ℂ ↦ ‖z‖ ^ 2)
      (show _ = (2 * π * Complex.I) ^ m * prinSymbol A a m x₀ ξ * 𝓕 v ξ from ?_)).trans ?_⟩
  · simp only [FourierTransform.fourier_sum, FourierTransform.fourier_smul, sum_apply,
      smul_apply, smul_eq_mul, fourier_mdir_apply, prinSymbol, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun α hα ↦ by
      rw [(Finset.mem_filter.1 hα).2, show (𝓕 φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ξ = 𝓕 v ξ from
        congrFun (fourier_coe φ) ξ]; ring
  · simp only [norm_mul, norm_pow, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; ring
theorem integral_norm_sq_frozenOp {v : EuclideanSpace ℝ (Fin n) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ‖frozenOp A a m x₀ v x‖ ^ 2 =
      ∫ ξ, (2 * π) ^ (2 * m) * ‖prinSymbol A a m x₀ ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2 := by
  obtain ⟨ψ, hψ, hFψ⟩ := exists_schwartz_frozenOp (A := A) (a := a) (m := m) hv hvc x₀
  rw [show (fun x ↦ ‖frozenOp A a m x₀ v x‖ ^ 2) = fun x ↦ ‖ψ x‖ ^ 2 from
    funext fun x ↦ by rw [hψ], ← integral_norm_sq_fourier]
  exact integral_congr_ae (ae_of_all _ hFψ)
theorem integrable_frozen_fourier {v : EuclideanSpace ℝ (Fin n) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun ξ ↦ (2 * π) ^ (2 * m) * ‖prinSymbol A a m x₀ ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2) := by
  obtain ⟨ψ, -, hFψ⟩ := exists_schwartz_frozenOp (A := A) (a := a) (m := m) hv hvc x₀
  simpa only [hFψ] using integrable_norm_sq_schwartz (𝓕 ψ)
end Symbol

section Helpers
variable {v : EuclideanSpace ℝ (Fin n) → ℂ}
private theorem iter_eq_zero' (k : ℕ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ tsupport v) :
    iteratedFDeriv ℝ k v x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_iteratedFDeriv_subset k h)
private theorem memLp_hsD' (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (k : ℕ) :
    MemLp (hsD k v) 2 volume :=
  memLp_two_of_continuous_hasCompactSupport
    (Real.continuous_sqrt.comp <| continuous_finsetSum _ fun _ _ ↦ ((continuous_eval_const _).comp
      (hv.continuous_iteratedFDeriv (by exact_mod_cast le_top))).norm.pow 2)
    (hvc.mono' fun _ hx ↦ not_not.1 fun h ↦ hx (by simp [hsD, pdT_apply, iter_eq_zero' k h]))
theorem exists_mdir_eq_ev (α : Fin n → ℕ) : ∃ J : Fin (mabs α) → Fin n, ∀ l, mdir α l = ev (J l) := by
  have h (l) : ∃ i, mdir α l = ev i := by
    have hmem : mdir α l ∈ mdirList α := List.get_mem _ _
    simp only [mdirList, List.mem_flatMap, List.mem_replicate] at hmem
    obtain ⟨i, -, -, hi⟩ := hmem; exact ⟨i, hi⟩
  choose J hJ using h; exact ⟨J, hJ⟩
theorem norm_pdT_le_hsD {k : ℕ} (J : Fin k → Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖pdT J v x‖ ≤ hsD k v x :=
  Real.le_sqrt_of_sq_le <| Finset.single_le_sum (f := fun J ↦ ‖pdT J v x‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ J)
theorem norm_pderiv_le_hsD (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖pderiv α v x‖ ≤ hsD (mabs α) v x := by
  obtain ⟨J, hJ⟩ := exists_mdir_eq_ev α
  exact (by rw [pderiv_eq_dT, pdT, dT_apply, dT_apply, funext hJ] : pderiv α v x = pdT J v x) ▸ norm_pdT_le_hsD J x
private theorem memLp_norm_sum_pderiv {S : Finset (Fin n → ℕ)}
    {c : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ} (hc : ∀ α ∈ S, Continuous (c α))
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    MemLp (fun x ↦ ‖∑ α ∈ S, c α x * pderiv α v x‖) 2 volume :=
  memLp_two_of_continuous_hasCompactSupport
    (continuous_finsetSum _ fun α hα ↦ (hc α hα).mul
      ((continuous_eval_const _).comp (hv.continuous_iteratedFDeriv (by exact_mod_cast le_top)))).norm
    (hvc.mono' fun _ hx ↦ not_not.1 fun h ↦ hx (by simp [pderiv, iter_eq_zero' _ h]))
end Helpers

section Estimate
variable {m : ℕ} {A : Finset (Fin n → ℕ)} {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}
theorem l2Norm_derivative_le_frozen_operator {c : ℝ} (hc : 0 < c) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hσ : ∀ ξ : EuclideanSpace ℝ (Fin n), c * ‖ξ‖ ^ m ≤ ‖prinSymbol A a m x₀ ξ‖)
    {v : EuclideanSpace ℝ (Fin n) → ℂ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    l2n (hsD m v) ≤ c⁻¹ * l2n (fun x ↦ ‖frozenOp A a m x₀ v x‖) := by
  have hP : MemLp (fun x ↦ ‖frozenOp A a m x₀ v x‖) 2 volume :=
    memLp_norm_sum_pderiv (fun _ _ ↦ continuous_const) hv hvc
  rw [l2Norm_eq_sqrt_integral_sq (memLp_hsD' hv hvc m), l2Norm_eq_sqrt_integral_sq hP,
    integral_hsD_sq hv hvc, integral_norm_sq_frozenOp hv hvc x₀,
    ← Real.sqrt_sq (inv_nonneg.2 hc.le), ← Real.sqrt_mul (sq_nonneg _), ← integral_const_mul]
  refine Real.sqrt_le_sqrt (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity)
    ((integrable_frozen_fourier hv hvc x₀).const_mul _) (ae_of_all _ fun ξ ↦ ?_))
  have h2 := pow_le_pow_left₀ (by positivity) ((le_inv_mul_iff₀ hc).2 (hσ ξ)) 2
  exact (by rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; ring :
      ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ m * ‖𝓕 v ξ‖ ^ 2 = (2 * π) ^ (2 * m) * (‖ξ‖ ^ m) ^ 2 * ‖𝓕 v ξ‖ ^ 2).trans_le
    ((by gcongr : _ ≤ (2 * π) ^ (2 * m) * (c⁻¹ * ‖prinSymbol A a m x₀ ξ‖) ^ 2 * ‖𝓕 v ξ‖ ^ 2).trans_eq (by ring))
theorem elliptic_estimate (hnm : 0 < n ∨ 1 ≤ m) (hA : ∀ α ∈ A, mabs α ≤ m)
    (ha : ∀ α ∈ A, Continuous (a α)) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hell : ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A a m x₀ ξ ≠ 0) :
    ∃ R₀ > 0, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ v : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ∞ v →
      HasCompactSupport v → tsupport v ⊆ Metric.ball x₀ R₀ →
      l2n (hsD m v) ≤ C₀ * (l2n (fun x ↦ ‖diffOp A a v x‖) + ∑ j ∈ Finset.range m, l2n (hsD j v)) := by
  obtain ⟨c, hc, hσ⟩ := exists_prinSymbol_lower_bound hnm hell
  set N : ℝ := (A.card : ℝ); set ε := c / (2 * (N + 1)); have hε : 0 < ε := by positivity
  set M := ε + ∑ β ∈ A, ‖a β x₀‖; have hM0 : 0 ≤ M := by positivity
  obtain ⟨δ, hδ, hδε⟩ := Metric.eventually_nhds_iff.1 <| (Filter.eventually_all_finset A).2
    fun α hα ↦ by simpa only [dist_eq_norm] using Metric.tendsto_nhds.1 ((ha α hα).tendsto x₀) ε hε
  refine ⟨δ, hδ, 2 * c⁻¹ * max 1 (M * N), by positivity, fun v hv hvc hsupp ↦ ?_⟩
  have hpt (x) : ‖frozenOp A a m x₀ v x‖ ≤ ‖diffOp A a v x‖ + (ε * N) * hsD m v x +
      (M * N) * ∑ j ∈ Finset.range m, hsD j v x := by
    have hS0 : 0 ≤ ∑ j ∈ Finset.range m, hsD j v x := Finset.sum_nonneg fun _ _ ↦ hsD_nonneg _ _ _
    have hm0 := hsD_nonneg m v x
    by_cases hx : x ∈ tsupport v; swap
    · simp [frozenOp, pderiv, iter_eq_zero' _ hx]; positivity
    rw [show frozenOp A a m x₀ v x = diffOp A a v x +
        ∑ α ∈ A, (if mabs α = m then a α x₀ - a α x else -a α x) * pderiv α v x by
      rw [frozenOp, Finset.sum_filter, diffOp, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ by split_ifs <;> ring]
    refine (norm_add_le _ _).trans ((add_le_add le_rfl <| (norm_sum_le _ _).trans <|
      Finset.sum_le_card_nsmul A _ (ε * hsD m v x + M * ∑ j ∈ Finset.range m, hsD j v x)
        fun α hα ↦ ?_).trans_eq (by simp [nsmul_eq_mul, N]; ring))
    have hαε := (hδε (Metric.mem_ball.1 (hsupp hx)) α hα).le
    rw [norm_mul]; split_ifs with hm
    · rw [norm_sub_rev]
      exact (mul_le_mul hαε (hm ▸ norm_pderiv_le_hsD α x) (norm_nonneg _) hε.le).trans
        (le_add_of_nonneg_right (by positivity))
    · have hαM : ‖-a α x‖ ≤ M := by
        rw [norm_neg]; linarith [norm_sub_norm_le (a α x) (a α x₀),
          Finset.single_le_sum (f := fun β ↦ ‖a β x₀‖) (fun _ _ ↦ norm_nonneg _) hα]
      exact (mul_le_mul hαM ((norm_pderiv_le_hsD α x).trans (Finset.single_le_sum
        (f := fun j ↦ hsD j v x) (fun _ _ ↦ hsD_nonneg _ _ _)
        (Finset.mem_range.2 (lt_of_le_of_ne (hA α hα) hm)))) (norm_nonneg _) hM0).trans
        (le_add_of_nonneg_left (by positivity))
  have hDv : MemLp (fun x ↦ ‖diffOp A a v x‖) 2 volume := memLp_norm_sum_pderiv ha hv hvc
  have hR1 := (memLp_hsD' hv hvc m).const_mul (ε * N)
  have hR2 := (memLp_finsetSum (Finset.range m) fun j _ ↦ memLp_hsD' hv hvc j).const_mul (M * N)
  have hF : MemLp (fun x ↦ ‖frozenOp A a m x₀ v x‖) 2 volume :=
    memLp_norm_sum_pderiv (fun _ _ ↦ continuous_const) hv hvc
  have hfrozen : l2n (fun x ↦ ‖frozenOp A a m x₀ v x‖) ≤ l2n (fun x ↦ ‖diffOp A a v x‖) +
      (ε * N) * l2n (hsD m v) + (M * N) * ∑ j ∈ Finset.range m, l2n (hsD j v) := by
    refine (l2Norm_le_of_abs_le ((hDv.add hR1).add hR2) hF.aestronglyMeasurable
      fun x ↦ (abs_of_nonneg (norm_nonneg _)).trans_le (hpt x)).trans
      ((l2Norm_add_le_alt (hDv.add hR1) hR2).trans ((add_le_add (l2Norm_add_le_alt hDv hR1) le_rfl).trans ?_))
    rw [l2Norm_const_mul, l2Norm_const_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have hY := l2Norm_finset_sum_le (Finset.range m) _ fun j _ ↦ memLp_hsD' hv hvc j; gcongr
  have hεN : c⁻¹ * (ε * N) * l2n (hsD m v) ≤ 1 / 2 * l2n (hsD m v) := by
    refine mul_le_mul_of_nonneg_right ?_ (l2Norm_nonneg_alt _)
    rw [show c⁻¹ * (ε * N) = N / (2 * (N + 1)) by simp only [ε]; field_simp,
      div_le_div_iff₀ (by positivity) two_pos]; linarith
  have hZY : l2n (fun x ↦ ‖diffOp A a v x‖) + M * N * ∑ j ∈ Finset.range m, l2n (hsD j v) ≤
      max 1 (M * N) * (l2n (fun x ↦ ‖diffOp A a v x‖) + ∑ j ∈ Finset.range m, l2n (hsD j v)) := by
    linarith [le_mul_of_one_le_left (l2Norm_nonneg_alt (fun x ↦ ‖diffOp A a v x‖)) (le_max_left 1 (M * N)),
      mul_le_mul_of_nonneg_right (le_max_right 1 (M * N))
        (Finset.sum_nonneg fun j (_ : j ∈ Finset.range m) ↦ l2Norm_nonneg_alt (hsD j v))]
  linarith [(l2Norm_derivative_le_frozen_operator hc hσ hv hvc).trans
    (mul_le_mul_of_nonneg_left hfrozen (inv_nonneg.2 hc.le)),
    mul_le_mul_of_nonneg_left hZY (show 0 ≤ 2 * c⁻¹ by positivity)]
end Estimate

section Pointwise
variable {v : EuclideanSpace ℝ (Fin n) → ℂ}
theorem integrable_fourier_weight (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (q : ℕ) :
    Integrable (fun ξ ↦ ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ q * ‖𝓕 v ξ‖ ^ 2) :=
  (integrable_finsetSum _ fun _ _ ↦ integrable_norm_sq_schwartz _).congr
    (ae_of_all _ (sum_norm_sq_fourier_pdT hv hvc q))
theorem integrable_inv_one_add_weight {σ : ℕ} (hσ : n < 2 * σ) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) ↦ (1 + ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ)⁻¹) := by
  have hr : (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) < (2 * σ : ℕ) := by
    simpa [finrank_euclideanSpace_fin] using mod_cast hσ
  refine ((integrable_one_add_norm hr).const_mul ((2 : ℝ) ^ (2 * σ))).mono'
    (Continuous.inv₀ (by fun_prop) fun _ ↦ by positivity).aestronglyMeasurable (ae_of_all _ fun ξ ↦ ?_)
  have hW : ‖ξ‖ ^ (2 * σ) ≤ ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ := by
    rw [pow_mul, mul_pow]
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (one_le_pow₀ (by linarith [Real.pi_gt_three])))
  have h1 : (1 + ‖ξ‖) ^ (2 * σ) ≤ 2 ^ (2 * σ) * (1 + ‖ξ‖ ^ (2 * σ)) := by
    rcases le_total ‖ξ‖ 1 with h | h
    · exact (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
        (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (by positivity)))
    · exact (pow_le_pow_left₀ (by positivity) (by linarith) (2 * σ)).trans
        ((mul_pow 2 ‖ξ‖ _).trans_le (by gcongr; linarith))
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
  exact (h1.trans (by gcongr)).trans_eq (mul_comm _ _)
theorem sobolev_pointwise : ∃ σ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EuclideanSpace ℝ (Fin n) → ℂ,
    ContDiff ℝ ∞ w → HasCompactSupport w → ∀ x, ‖w x‖ ≤ C * (l2n (hsD 0 w) + l2n (hsD σ w)) := by
  set σ := n / 2 + 1
  set W : EuclideanSpace ℝ (Fin n) → ℝ := fun ξ ↦ 1 + ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ
  have hWpos (ξ) : 0 < W ξ := by positivity
  have hI₁int : Integrable (fun ξ ↦ (W ξ)⁻¹) := integrable_inv_one_add_weight (by omega)
  have hI₁ : 0 ≤ ∫ ξ, (W ξ)⁻¹ := integral_nonneg fun ξ ↦ (inv_pos.2 (hWpos ξ)).le
  refine ⟨σ, Real.sqrt (∫ ξ, (W ξ)⁻¹), Real.sqrt_nonneg _, fun w hw hwc x ↦ ?_⟩
  set φ := hwc.toSchwartzMap hw
  have hFint : Integrable (𝓕 w) := (𝓕 φ).integrable.congr (ae_of_all _ fun ξ ↦ congrFun (fourier_coe φ) ξ)
  have hx1 : ‖w x‖ ≤ ∫ ξ, ‖𝓕 w ξ‖ := by
    conv_lhs => rw [← hw.continuous.fourierInv_fourier_eq φ.integrable hFint, Real.fourierInv_eq]
    exact (norm_integral_le_integral_norm _).trans_eq
      (integral_congr_ae (ae_of_all _ fun _ ↦ by simp [Circle.norm_smul]))
  have hWint : Integrable (fun ξ ↦ W ξ * ‖𝓕 w ξ‖ ^ 2) :=
    ((integrable_fourier_weight hw hwc 0).add (integrable_fourier_weight hw hwc σ)).congr
      (ae_of_all _ fun _ ↦ by simp only [W, Pi.add_apply, pow_zero]; ring)
  set S := l2n (hsD 0 w) + l2n (hsD σ w)
  have hS0 : 0 ≤ S := add_nonneg (l2Norm_nonneg_alt _) (l2Norm_nonneg_alt _)
  have hWsq : ∫ ξ, W ξ * ‖𝓕 w ξ‖ ^ 2 ≤ S ^ 2 := by
    rw [← integral_congr_ae (ae_of_all _ fun ξ ↦ (by simp only [W, pow_zero]; ring :
      ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ 0 * ‖𝓕 w ξ‖ ^ 2 + ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ * ‖𝓕 w ξ‖ ^ 2 =
        W ξ * ‖𝓕 w ξ‖ ^ 2)), integral_add (integrable_fourier_weight hw hwc 0)
      (integrable_fourier_weight hw hwc σ), ← integral_hsD_sq hw hwc, ← integral_hsD_sq hw hwc,
      ← Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _), ← l2Norm_eq_sqrt_integral_sq (memLp_hsD' hw hwc 0),
      ← Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _), ← l2Norm_eq_sqrt_integral_sq (memLp_hsD' hw hwc σ)]
    linarith [add_sq (l2n (hsD 0 w)) (l2n (hsD σ w)),
      mul_nonneg (l2Norm_nonneg_alt (hsD 0 w)) (l2Norm_nonneg_alt (hsD σ w))]
  have hd := discrim_le_zero (a := ∫ ξ, (W ξ)⁻¹) (b := -(2 * ∫ ξ, ‖𝓕 w ξ‖)) (c := S ^ 2) fun t ↦ by
    have hle := integral_mono (hFint.norm.const_mul (2 * t)) ((hI₁int.const_mul (t * t)).add hWint) fun ξ ↦ by
      have hW := hWpos ξ; have : 0 ≤ (t - W ξ * ‖𝓕 w ξ‖) ^ 2 / W ξ := by positivity
      have e : (t * t) * (W ξ)⁻¹ + W ξ * ‖𝓕 w ξ‖ ^ 2 - 2 * t * ‖𝓕 w ξ‖ =
          (t - W ξ * ‖𝓕 w ξ‖) ^ 2 / W ξ := by field_simp; ring
      show 2 * t * ‖𝓕 w ξ‖ ≤ _ + _; linarith
    have heq := integral_add (hI₁int.const_mul (t * t)) hWint
    simp only [Pi.add_apply] at hle heq; rw [integral_const_mul] at hle heq; linarith
  exact hx1.trans (abs_le_of_sq_le_sq'
    (by rw [discrim] at hd; rw [mul_pow, Real.sq_sqrt hI₁]; linarith) (by positivity)).2
end Pointwise
end
end GroundTheory.Automorphic.Sobolev
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoGarding =====

-- ===== clump member: GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoSeries =====
-- clump-header: {"m": "GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoSeries", "h": "module\n\npublic import Mathlib.Analysis.Calculus.IteratedDeriv.Defs\npublic import Mathlib.Analysis.LocallyConvex.AbsConvexOpen\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\npublic import Mathlib.Analysis.Analytic.IteratedFDeriv\npublic import Mathlib.Analysis.Calculus.Taylor\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Analysis.Calculus.Deriv.Add\npublic import Mathlib.Analysis.Calculus.Deriv.Mul\n\n"}
section -- clump:auto
@[expose] public section

namespace GroundTheory.Automorphic.Sobolev

open scoped ContDiff NNReal ENNReal Topology
open Set Filter

noncomputable section

section Converse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem hasDerivAt_iteratedFDeriv_line {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (x₀ y : E) (k : ℕ) {t : ℝ} (ht : x₀ + t • y ∈ s) :
    HasDerivAt (fun τ : ℝ ↦ iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y))
      (iteratedFDeriv ℝ (k + 1) f (x₀ + t • y) (fun _ ↦ y)) t := by
  have hz : HasDerivAt (fun τ : ℝ ↦ x₀ + τ • y) y t := by
    simpa using ((hasDerivAt_id t).smul_const y).const_add x₀
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) (x₀ + t • y) :=
    (hf.contDiffAt (hs.mem_nhds ht)).differentiableAt_iteratedFDeriv (by
      exact_mod_cast ENat.natCast_lt_top k)
  have h1 := hd.hasFDerivAt.comp_hasDerivAt t hz
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F
    (fun _ ↦ y)).hasFDerivAt.comp_hasDerivAt t h1
  have e : iteratedFDeriv ℝ (k + 1) f (x₀ + t • y) (fun _ ↦ y) =
      (fderiv ℝ (iteratedFDeriv ℝ k f) (x₀ + t • y) y) (fun _ ↦ y) := by
    rw [iteratedFDeriv_succ_apply_left]; rfl
  rw [e]
  exact h2

theorem iteratedDeriv_line_eq {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (x₀ y : E) (k : ℕ) {t : ℝ} (ht : x₀ + t • y ∈ s) :
    iteratedDeriv k (fun τ : ℝ ↦ f (x₀ + τ • y)) t =
      iteratedFDeriv ℝ k f (x₀ + t • y) (fun _ ↦ y) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    have hU : IsOpen {τ : ℝ | x₀ + τ • y ∈ s} := hs.preimage (by fun_prop)
    have hev : iteratedDeriv k (fun τ : ℝ ↦ f (x₀ + τ • y)) =ᶠ[𝓝 t]
        fun τ ↦ iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y) := by
      filter_upwards [hU.mem_nhds ht] with τ hτ using ih hτ
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact (hasDerivAt_iteratedFDeriv_line hs hf x₀ y k ht).deriv

theorem analyticAt_of_norm_iteratedFDeriv_le {f : E → F} {x₀ : E} {r C M : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball x₀ r))
    (hb : ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k.factorial) :
    AnalyticAt ℝ f x₀ := by
  set M' : ℝ := |M| + 1 with hM'
  have hM'pos : 0 < M' := by positivity
  have hb' : ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ |C| * M' ^ k * k.factorial := by
    intro y hy k
    refine (hb y hy k).trans ?_
    have h1 : C * M ^ k ≤ |C| * M' ^ k := by
      calc C * M ^ k ≤ |C * M ^ k| := le_abs_self _
        _ = |C| * |M| ^ k := by rw [abs_mul, abs_pow]
        _ ≤ |C| * M' ^ k := by
          gcongr
          linarith
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  set ρ : ℝ := min r (1 / M') / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hρr : ρ < r := by
    have := min_le_left r (1 / M')
    rw [hρ]; linarith
  have hρM : M' * ρ ≤ 1 / 2 := by
    have h := min_le_right r (1 / M')
    rw [hρ]
    have : M' * (min r (1 / M')) ≤ 1 := by
      calc M' * min r (1 / M') ≤ M' * (1 / M') := by gcongr
        _ = 1 := by field_simp
    linarith
  set p : FormalMultilinearSeries ℝ E F :=
    fun k ↦ ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k f x₀ with hpdef
  have hx₀ : x₀ ∈ Metric.ball x₀ r := Metric.mem_ball_self hr
  have hp : ∀ k, ‖p k‖ ≤ |C| * M' ^ k := by
    intro k
    have h := hb' x₀ hx₀ k
    have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    simp only [hpdef, norm_smul, norm_inv, Real.norm_natCast]
    rw [inv_mul_le_iff₀ hk]
    linarith
  refine ⟨p, ENNReal.ofReal ρ, ?_, ?_, ?_⟩
  · have : ((Real.toNNReal ρ : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
      refine p.le_radius_of_bound (|C|) fun k ↦ ?_
      rw [Real.coe_toNNReal _ hρpos.le]
      calc ‖p k‖ * ρ ^ k ≤ |C| * M' ^ k * ρ ^ k := by gcongr; exact hp k
        _ = |C| * (M' * ρ) ^ k := by ring_nf
        _ ≤ |C| * 1 := by
          gcongr
          exact pow_le_one₀ (by positivity) (by linarith)
        _ = |C| := mul_one _
    exact this
  · simpa using hρpos
  · intro y hy
    have hy' : ‖y‖ < ρ := by
      simpa [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm, ENNReal.ofReal,
        ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hρpos.le] using hy

    set q : ℝ := M' * ‖y‖ with hq
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q < 1 := by
      have : M' * ‖y‖ < M' * ρ := mul_lt_mul_of_pos_left hy' hM'pos
      linarith
    have hterm : ∀ k, ‖p k (fun _ ↦ y)‖ ≤ |C| * q ^ k := by
      intro k
      calc ‖p k (fun _ ↦ y)‖ ≤ ‖p k‖ * ∏ _i : Fin k, ‖y‖ := (p k).le_opNorm _
        _ = ‖p k‖ * ‖y‖ ^ k := by simp
        _ ≤ |C| * M' ^ k * ‖y‖ ^ k := by gcongr; exact hp k
        _ = |C| * q ^ k := by rw [hq, mul_pow]; ring
    have hsum : Summable fun k ↦ ‖p k (fun _ ↦ y)‖ :=
      Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm
        ((summable_geometric_of_lt_one hq0 hq1).mul_left _)
    rw [hasSum_iff_tendsto_nat_of_summable_norm hsum]
    rw [← Filter.tendsto_add_atTop_iff_nat 1]

    set g : ℝ → F := fun τ ↦ f (x₀ + τ • y) with hg
    have hline : ∀ τ ∈ Icc (0 : ℝ) 1, x₀ + τ • y ∈ Metric.ball x₀ r := by
      intro τ hτ
      rw [Metric.mem_ball, dist_self_add_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hτ.1]
      calc τ * ‖y‖ ≤ 1 * ‖y‖ := by gcongr; exact hτ.2
        _ < r := by linarith
    have hgAt : ∀ τ ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ g τ := by
      intro τ hτ
      have h1 : ContDiffAt ℝ ∞ f (x₀ + τ • y) :=
        hf.contDiffAt (Metric.isOpen_ball.mem_nhds (hline τ hτ))
      exact h1.comp τ (by fun_prop)
    have hder : ∀ k, ∀ τ ∈ Icc (0 : ℝ) 1, iteratedDerivWithin k g (Icc 0 1) τ =
        iteratedFDeriv ℝ k f (x₀ + τ • y) (fun _ ↦ y) := by
      intro k τ hτ
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
        ((hgAt τ hτ).of_le (by exact_mod_cast le_top)) hτ]
      exact iteratedDeriv_line_eq Metric.isOpen_ball hf x₀ y k (hline τ hτ)
    have hrem : ∀ N : ℕ, ‖(∑ k ∈ Finset.range (N + 1), p k (fun _ ↦ y)) - f (x₀ + y)‖ ≤
        |C| * (((N + 1 : ℕ) : ℝ) * q ^ (N + 1)) := by
      intro N
      have hgC : ContDiffOn ℝ (N + 1) g (Icc 0 1) := fun τ hτ ↦
        ((hgAt τ hτ).of_le (by exact_mod_cast le_top)).contDiffWithinAt
      have hbd : ∀ τ ∈ Icc (0 : ℝ) 1, ‖iteratedDerivWithin (N + 1) g (Icc 0 1) τ‖ ≤
          |C| * M' ^ (N + 1) * ((N + 1).factorial : ℝ) * ‖y‖ ^ (N + 1) := by
        intro τ hτ
        rw [hder (N + 1) τ hτ]
        calc ‖iteratedFDeriv ℝ (N + 1) f (x₀ + τ • y) (fun _ ↦ y)‖
            ≤ ‖iteratedFDeriv ℝ (N + 1) f (x₀ + τ • y)‖ * ∏ _i : Fin (N + 1), ‖y‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ = ‖iteratedFDeriv ℝ (N + 1) f (x₀ + τ • y)‖ * ‖y‖ ^ (N + 1) := by simp
          _ ≤ |C| * M' ^ (N + 1) * ((N + 1).factorial : ℝ) * ‖y‖ ^ (N + 1) := by
              gcongr
              exact hb' _ (hline τ hτ) _
      have hT := taylor_mean_remainder_bound (f := g) (n := N) hgC
        (right_mem_Icc.2 zero_le_one) hbd
      have hsumeq : taylorWithinEval g N (Icc 0 1) 0 1 =
          ∑ k ∈ Finset.range (N + 1), p k (fun _ ↦ y) := by
        rw [taylor_within_apply]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [hder k 0 (left_mem_Icc.2 zero_le_one)]
        simp [hpdef]
      rw [hsumeq] at hT
      have hg1 : g 1 = f (x₀ + y) := by simp [hg]
      rw [hg1, norm_sub_rev] at hT
      refine hT.trans (le_of_eq ?_)
      rw [Nat.factorial_succ]
      have hN : (N.factorial : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      rw [hq, mul_pow]
      ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun N : ℕ ↦ |C| * (((N + 1 : ℕ) : ℝ) * q ^ (N + 1))) atTop (𝓝 0) := by
      have h := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).comp (tendsto_add_atTop_nat 1)
      simpa using h.const_mul |C|
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hrem hlim

end Converse

section Forward

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

theorem norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall {f : E → F}
    {q : FormalMultilinearSeries ℝ E F} {y : E} {R : ℝ≥0∞} (h : HasFPowerSeriesOnBall f q y R)
    (k : ℕ) : ‖iteratedFDeriv ℝ k f y‖ ≤ k.factorial * ‖q k‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [h.iteratedFDeriv_eq_sum_of_completeSpace v]
  calc ‖∑ σ : Equiv.Perm (Fin k), q k (fun i ↦ v (σ i))‖
      ≤ ∑ σ : Equiv.Perm (Fin k), ‖q k (fun i ↦ v (σ i))‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), ‖q k‖ * ∏ i, ‖v i‖ := by
        gcongr with σ
        refine ((q k).le_opNorm _).trans (le_of_eq ?_)
        congr 1
        exact Equiv.prod_comp σ (fun i ↦ ‖v i‖)
    _ = k.factorial * ‖q k‖ * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]
        ring

theorem nnnorm_changeOrigin_le_of_bound (p : FormalMultilinearSeries ℝ E F) {ρ K : ℝ≥0}
    (hρ : 0 < ρ) (hK : ∀ n, ‖p n‖₊ ≤ K / ρ ^ n) {z : E} (hz : 4 * ‖z‖₊ ≤ ρ)
    (hzr : (‖z‖₊ : ℝ≥0∞) < p.radius) (k : ℕ) :
    ‖p.changeOrigin z k‖₊ ≤ 2 * (K * (2 / ρ) ^ k) := by
  have hsum := p.changeOriginSeries_summable_aux₂ hzr k
  have h1 := p.nnnorm_changeOrigin_le k hzr
  rw [← ENNReal.coe_le_coe] at h1 ⊢
  refine h1.trans ?_
  rw [ENNReal.coe_tsum hsum, ENNReal.tsum_sigma']
  have hterm : ∀ l : ℕ, ∑' _b : { s : Finset (Fin (k + l)) // s.card = l },
      ((‖p (k + l)‖₊ * ‖z‖₊ ^ l : ℝ≥0) : ℝ≥0∞)
      ≤ ((K * (2 / ρ) ^ k * (2⁻¹) ^ l : ℝ≥0) : ℝ≥0∞) := by
    intro l
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_finset_len,
      Fintype.card_fin, nsmul_eq_mul, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
      ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    have hK' := hK (k + l)
    rw [← NNReal.coe_le_coe] at hK'
    push_cast at hK' ⊢
    have hz' : 4 * ‖z‖ ≤ (ρ : ℝ) := by exact_mod_cast hz
    have hch : ((k + l).choose l : ℝ) ≤ 2 ^ (k + l) := by
      exact_mod_cast Nat.choose_le_two_pow _ _
    have hρ' : (0 : ℝ) < ρ := hρ
    calc ((k + l).choose l : ℝ) * (‖p (k + l)‖ * ‖z‖ ^ l)
        ≤ 2 ^ (k + l) * ((K : ℝ) / (ρ : ℝ) ^ (k + l) * ((ρ : ℝ) / 4) ^ l) := by
          gcongr
          linarith
      _ = (K : ℝ) * (2 / (ρ : ℝ)) ^ k * (2⁻¹) ^ l := by
          have h4 : (4 : ℝ) ^ l = 2 ^ l * 2 ^ l := by rw [← mul_pow]; norm_num
          rw [pow_add, pow_add, div_pow, div_pow, inv_pow, h4]
          field_simp
  refine (ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_)
  simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv_two]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  push_cast
  ring

theorem exists_norm_iteratedFDeriv_le_of_analyticAt {f : E → F} {x₀ : E}
    (hf : AnalyticAt ℝ f x₀) :
    ∃ r > 0, ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k.factorial := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨ρ, hρ0', hρR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  have hρ0 : 0 < ρ := ENNReal.coe_pos.1 hρ0'
  obtain ⟨K, hK0, hK⟩ := p.norm_le_div_pow_of_pos_of_lt_radius hρ0 (hρR.trans_le hp.r_le)
  set K' : ℝ≥0 := ⟨K, hK0.le⟩ with hK'def
  have hK' : ∀ n, ‖p n‖₊ ≤ K' / ρ ^ n := fun n ↦ by
    rw [← NNReal.coe_le_coe]; push_cast; exact hK n
  have hρ' : (0 : ℝ) < ρ := hρ0
  refine ⟨(ρ : ℝ) / 4, by positivity, 2 * K, 2 / ρ, by positivity, by positivity,
    fun y hy k ↦ ?_⟩
  set z := y - x₀ with hzdef
  have hz : ‖z‖ < (ρ : ℝ) / 4 := by rwa [Metric.mem_ball, dist_eq_norm] at hy
  have hzρ : ‖z‖₊ < ρ := by
    rw [← NNReal.coe_lt_coe, coe_nnnorm]; linarith [norm_nonneg z]
  have hzR : (‖z‖₊ : ℝ≥0∞) < R := lt_trans (by exact_mod_cast hzρ) hρR
  have hq := hp.changeOrigin hzR
  have hxy : x₀ + z = y := by simp [hzdef]
  rw [hxy] at hq
  refine (norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall hq k).trans ?_
  have hb := nnnorm_changeOrigin_le_of_bound p hρ0 hK'
    (z := z) (by rw [← NNReal.coe_le_coe]; push_cast; linarith) (hzR.trans_le hp.r_le) k
  rw [← NNReal.coe_le_coe] at hb
  push_cast at hb
  have hb' : ‖p.changeOrigin z k‖ ≤ 2 * (K * (2 / ρ) ^ k) := hb
  calc (k.factorial : ℝ) * ‖p.changeOrigin z k‖ ≤ k.factorial * (2 * (K * (2 / ρ) ^ k)) := by
        gcongr
    _ = 2 * K * (2 / ρ) ^ k * k.factorial := by ring

end Forward

end

end GroundTheory.Automorphic.Sobolev
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoSeries =====

-- ===== clump member: GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoelliptic =====
-- clump-header: {"m": "GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoelliptic", "h": "module\n\npublic import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoStep\nimport GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoCalc\nimport GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoCutoff\npublic import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoGarding\npublic import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoSeries\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.Order.CompletePartialOrder\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Mathlib.Topology.UniformSpace.Uniformizable\n\n"}
section -- clump:auto
@[expose] public section

namespace GroundTheory.Automorphic.Sobolev

open MeasureTheory Finset
open scoped ContDiff

noncomputable section

variable {n : ℕ}

theorem powMul_self_le {s i q : ℕ} (h : i + q ≤ s) : (s : ℝ) ^ i * (q : ℝ) ^ q ≤ (s : ℝ) ^ s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · obtain ⟨rfl, rfl⟩ : i = 0 ∧ q = 0 := by omega
    simp
  · have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    calc (s : ℝ) ^ i * (q : ℝ) ^ q ≤ (s : ℝ) ^ i * (s : ℝ) ^ q := by
          gcongr; exact_mod_cast (by omega : q ≤ s)
      _ = (s : ℝ) ^ (i + q) := by rw [pow_add]
      _ ≤ (s : ℝ) ^ s := pow_le_pow_right₀ hs' h

theorem pow_self_le_exp_mul_factorial (p : ℕ) :
    (p : ℝ) ^ p ≤ Real.exp 1 ^ p * p.factorial := by
  have h := Real.pow_div_factorial_le_exp (x := (p : ℝ)) (Nat.cast_nonneg _) p
  rw [div_le_iff₀ (by positivity), ← Real.exp_one_pow] at h
  exact h

theorem factorial_add_le (k σ : ℕ) :
    ((k + σ).factorial : ℝ) ≤ 2 ^ (k + σ) * k.factorial * σ.factorial := by
  have h := Nat.add_choose_mul_factorial_mul_factorial k σ
  have hc : (k + σ).choose σ ≤ 2 ^ (k + σ) := Nat.choose_le_two_pow _ _
  have : (k + σ).factorial ≤ 2 ^ (k + σ) * k.factorial * σ.factorial := by
    rw [← h]
    gcongr
  exact_mod_cast this

theorem l2Norm_sqrt_sum_derivative_cutoff_power_le {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiff ℝ ∞ u)
    (hu_c : HasCompactSupport u) {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {K : ℝ} (hK0 : 0 ≤ K) {L₀ : ℕ}
    (hK : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ L₀ → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i))
    {k s j : ℕ} (hjL : j ≤ L₀) (hjs : j + k ≤ s) :
    l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n,
        hsD j (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x ^ 2)) ≤
      ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) * wN χ u (ij.2 + k) := by
  have mem : ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, Continuous f →
      (∀ x, x ∉ tsupport u → f x = 0) → MemLp f 2 volume := fun hc hz ↦
    memLp_two_of_continuous_hasCompactSupport hc (HasCompactSupport.intro hu_c hz)
  have memg : ∀ q, MemLp (fun x ↦ χ x ^ q * hsD q u x) 2 volume := fun q ↦
    mem ((hχ.continuous.pow q).mul (continuous_hsD hu q)) fun x hx ↦ by
      rw [hsD_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.1 hx), mul_zero]
  have memR : MemLp (fun x ↦ ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) *
      (χ x ^ (ij.2 + k) * hsD (ij.2 + k) u x)) 2 volume :=
    memLp_sum_mul _ _ _ fun ij _ ↦ memg _
  have hvC : ∀ I : Fin k → Fin n, ContDiff ℝ ∞ (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) :=
    fun I ↦ (contDiff_weight hχ s).mul (contDiff_pdT hu I)
  have hcont : Continuous (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n,
      hsD j (fun y ↦ ((χ y : ℂ)) ^ s * pdT I u y) x ^ 2)) :=
    (continuous_finsetSum _ fun I _ ↦ (continuous_hsD (hvC I) j).pow 2).sqrt
  refine (l2Norm_le_of_abs_le memR hcont.aestronglyMeasurable fun x ↦ ?_).trans
    (l2Norm_sum_const_mul_le _ _ (fun _ _ ↦ by positivity) _ fun ij _ ↦ memg _)
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact sqrt_sum_hsD_weight_le hu hχ h01 hK0 hK hjL hjs x

theorem hsD_le_of_sobolev {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiff ℝ ∞ u)
    (hu_c : HasCompactSupport u) {χ : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {K : ℝ} (hK0 : 0 ≤ K) {L₀ : ℕ}
    (hK : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ L₀ → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i))
    {σ : ℕ} (hσL : σ ≤ L₀) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsob : ∀ w : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ∞ w → HasCompactSupport w →
      ∀ x, ‖w x‖ ≤ CS * (l2n (hsD 0 w) + l2n (hsD σ w)))
    (k : ℕ) {y : EuclideanSpace ℝ (Fin n)} (hy : χ y = 1) :
    hsD k u y ≤ CS * ((∑ ij ∈ antidiagonal 0, (Nat.choose 0 ij.1 : ℝ) *
        (K * ((k + σ : ℕ) : ℝ) ^ ij.1) * wN χ u (ij.2 + k)) +
      ∑ ij ∈ antidiagonal σ, (σ.choose ij.1 : ℝ) * (K * ((k + σ : ℕ) : ℝ) ^ ij.1) *
        wN χ u (ij.2 + k)) := by
  set s := k + σ with hs
  set w : (Fin k → Fin n) → EuclideanSpace ℝ (Fin n) → ℂ :=
    fun I z ↦ ((χ z : ℂ)) ^ s * pdT I u z with hw
  have hwC : ∀ I, ContDiff ℝ ∞ (w I) := fun I ↦ (contDiff_weight hχ s).mul (contDiff_pdT hu I)
  have hwc : ∀ I, HasCompactSupport (w I) := by
    intro I
    refine HasCompactSupport.intro hu_c fun x hx ↦ ?_
    have := (dT_eventuallyEq_zero_of_not_mem_tsupport hx (fun l ↦ ev (I l))).self_of_nhds
    simp only [hw, pdT]
    rw [this, mul_zero]
  have memh : ∀ j I, MemLp (hsD j (w I)) 2 volume := fun j I ↦
    memLp_two_of_continuous_hasCompactSupport (continuous_hsD (hwC I) j) (by
      refine HasCompactSupport.intro (hwc I) fun x hx ↦ ?_
      exact hsD_eq_zero_of_eventuallyEq_zero (notMem_tsupport_iff_eventuallyEq.1 hx) j)
  have hpt : ∀ I, ‖pdT I u y‖ ≤ CS * (l2n (hsD 0 (w I)) + l2n (hsD σ (w I))) := by
    intro I
    have h := hsob (w I) (hwC I) (hwc I) y
    simp only [hw, hy, Complex.ofReal_one, one_pow, one_mul] at h
    exact h
  have e0 : l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, hsD 0 (w I) x ^ 2)) =
      Real.sqrt (∑ I : Fin k → Fin n, l2n (hsD 0 (w I)) ^ 2) :=
    l2Norm_sqrt_sum_sq_eq _ fun I ↦ memh 0 I
  have eσ : l2n (fun x ↦ Real.sqrt (∑ I : Fin k → Fin n, hsD σ (w I) x ^ 2)) =
      Real.sqrt (∑ I : Fin k → Fin n, l2n (hsD σ (w I)) ^ 2) :=
    l2Norm_sqrt_sum_sq_eq _ fun I ↦ memh σ I
  have h0 := l2Norm_sqrt_sum_derivative_cutoff_power_le hu hu_c hχ h01 hK0 hK (k := k) (s := s) (j := 0)
    (Nat.zero_le _) (by omega)
  have hσ := l2Norm_sqrt_sum_derivative_cutoff_power_le hu hu_c hχ h01 hK0 hK (k := k) (s := s) (j := σ)
    hσL (by omega)
  calc hsD k u y = Real.sqrt (∑ I : Fin k → Fin n, ‖pdT I u y‖ ^ 2) := rfl
    _ ≤ Real.sqrt (∑ I : Fin k → Fin n,
          (CS * (l2n (hsD 0 (w I)) + l2n (hsD σ (w I)))) ^ 2) :=
        sqrt_sum_sq_mono fun I ↦ ⟨norm_nonneg _, hpt I⟩
    _ = CS * Real.sqrt (∑ I : Fin k → Fin n, (l2n (hsD 0 (w I)) + l2n (hsD σ (w I))) ^ 2) := by
        rw [sqrt_sum_sq_const_mul, abs_of_nonneg hCS]
    _ ≤ CS * (Real.sqrt (∑ I : Fin k → Fin n, l2n (hsD 0 (w I)) ^ 2) +
          Real.sqrt (∑ I : Fin k → Fin n, l2n (hsD σ (w I)) ^ 2)) :=
        mul_le_mul_of_nonneg_left (sqrt_sum_sq_add_le _ _) hCS
    _ ≤ _ := by
        rw [← e0, ← eσ]
        exact mul_le_mul_of_nonneg_left (add_le_add h0 hσ) hCS

theorem exists_norm_iteratedFDeriv_le_of_wN {u : EuclideanSpace ℝ (Fin n) → ℂ}
    (hu : ContDiff ℝ ∞ u) (hu_c : HasCompactSupport u) {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) {K : ℝ} (hK0 : 0 ≤ K) {L₀ : ℕ}
    (hK : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ L₀ → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i))
    {σ : ℕ} (hσL : σ ≤ L₀) {CS : ℝ} (hCS : 0 ≤ CS)
    (hsob : ∀ w : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ∞ w → HasCompactSupport w →
      ∀ x, ‖w x‖ ≤ CS * (l2n (hsD 0 w) + l2n (hsD σ w)))
    {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hN : ∀ p : ℕ, wN χ u p ≤ B * L ^ p * (p : ℝ) ^ p) :
    ∃ C M : ℝ, ∀ (k : ℕ) (y : EuclideanSpace ℝ (Fin n)), χ y = 1 →
      ‖iteratedFDeriv ℝ k u y‖ ≤ C * M ^ k * k.factorial := by
  set e := Real.exp 1
  refine ⟨CS * (2 * 2 ^ σ * K * B) * (σ.factorial * (2 * e * L) ^ σ), 2 * e * L, fun k y hy ↦ ?_⟩
  set s := k + σ with hs

  have hterm : ∀ j, j ≤ σ → ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) *
      (K * ((k + σ : ℕ) : ℝ) ^ ij.1) * wN χ u (ij.2 + k) ≤ 2 ^ σ * K * (B * L ^ s * (s : ℝ) ^ s) := by
    intro j hj
    calc ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) * (K * ((k + σ : ℕ) : ℝ) ^ ij.1) *
          wN χ u (ij.2 + k)
        ≤ ∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ) * K * (B * L ^ s * (s : ℝ) ^ s) := by
          refine Finset.sum_le_sum fun ij hij ↦ ?_
          have h1 : ij.1 + ij.2 = j := mem_antidiagonal.1 hij
          have hb := hN (ij.2 + k)
          have hp := powMul_self_le (s := s) (i := ij.1) (q := ij.2 + k) (by omega)
          have hLq : L ^ (ij.2 + k) ≤ L ^ s := pow_le_pow_right₀ hL (by omega)
          calc (j.choose ij.1 : ℝ) * (K * ((k + σ : ℕ) : ℝ) ^ ij.1) * wN χ u (ij.2 + k)
              ≤ (j.choose ij.1 : ℝ) * (K * (s : ℝ) ^ ij.1) *
                  (B * L ^ (ij.2 + k) * ((ij.2 + k : ℕ) : ℝ) ^ (ij.2 + k)) := by
                gcongr
            _ = (j.choose ij.1 : ℝ) * K * B * (L ^ (ij.2 + k) *
                  ((s : ℝ) ^ ij.1 * ((ij.2 + k : ℕ) : ℝ) ^ (ij.2 + k))) := by ring
            _ ≤ (j.choose ij.1 : ℝ) * K * B * (L ^ s * (s : ℝ) ^ s) := by gcongr
            _ = _ := by ring
      _ = (∑ ij ∈ antidiagonal j, (j.choose ij.1 : ℝ)) * K * (B * L ^ s * (s : ℝ) ^ s) := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ 2 ^ σ * K * (B * L ^ s * (s : ℝ) ^ s) := by
          rw [sum_antidiagonal_choose_eq]
          have : (0 : ℝ) ≤ B * L ^ s * (s : ℝ) ^ s := by positivity
          gcongr
          · norm_num
  have hmain := hsD_le_of_sobolev hu hu_c hχ h01 hK0 hK hσL hCS hsob k hy
  have hss : (s : ℝ) ^ s ≤ e ^ s * (2 ^ s * k.factorial * σ.factorial) :=
    (pow_self_le_exp_mul_factorial s).trans (by gcongr; exact factorial_add_le k σ)
  calc ‖iteratedFDeriv ℝ k u y‖ ≤ hsD k u y := norm_iteratedFDeriv_le_hsD k u y
    _ ≤ CS * (2 ^ σ * K * (B * L ^ s * (s : ℝ) ^ s) + 2 ^ σ * K * (B * L ^ s * (s : ℝ) ^ s)) :=
        hmain.trans (mul_le_mul_of_nonneg_left (add_le_add (hterm 0 (Nat.zero_le _))
          (hterm σ le_rfl)) hCS)
    _ = CS * (2 * 2 ^ σ * K * B) * (L ^ s * (s : ℝ) ^ s) := by ring
    _ ≤ CS * (2 * 2 ^ σ * K * B) * (L ^ s * (e ^ s * (2 ^ s * k.factorial * σ.factorial))) := by
        have : 0 ≤ CS * (2 * 2 ^ σ * K * B) := by positivity
        gcongr
    _ = CS * (2 * 2 ^ σ * K * B) * (σ.factorial * (2 * e * L) ^ σ) * (2 * e * L) ^ k *
          k.factorial := by
        rw [hs]; ring

theorem exists_coef_bound {A : Finset (Fin n → ℕ)}
    {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (ha : ∀ α ∈ A, AnalyticAt ℝ (a α) x₀) :
    ∃ ρ > 0, ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ α ∈ A, ∀ y ∈ Metric.ball x₀ ρ, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k (a α) y‖ ≤ C * M ^ k * k.factorial := by
  classical
  have h := fun α (hα : α ∈ A) ↦ exists_norm_iteratedFDeriv_le_of_analyticAt (ha α hα)
  choose! r hr C M hC hM hb using h
  have hev : ∀ᶠ y in nhds x₀, ∀ α ∈ A, y ∈ Metric.ball x₀ (r α) :=
    (Filter.eventually_all_finset A).2 fun α hα ↦ Metric.ball_mem_nhds x₀ (hr α hα)
  obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨ρ, hρ, ∑ α ∈ A, C α, ∑ α ∈ A, M α, Finset.sum_nonneg fun α hα ↦ hC α hα,
    Finset.sum_nonneg fun α hα ↦ hM α hα, fun α hα y hy k ↦ ?_⟩
  have h1 : C α ≤ ∑ β ∈ A, C β := Finset.single_le_sum (fun β hβ ↦ hC β hβ) hα
  have h2 : M α ≤ ∑ β ∈ A, M β := Finset.single_le_sum (fun β hβ ↦ hM β hβ) hα
  have hC0 := hC α hα
  have hM0 := hM α hα
  have hS0 : 0 ≤ ∑ β ∈ A, C β := le_trans hC0 h1
  calc ‖iteratedFDeriv ℝ k (a α) y‖ ≤ C α * M α ^ k * k.factorial :=
        hb α hα y (hρb y hy α hα) k
    _ ≤ (∑ β ∈ A, C β) * (∑ β ∈ A, M β) ^ k * k.factorial := by gcongr

theorem analyticAt_of_elliptic_of_pos (hn : 0 < n) {m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    {A : Finset (Fin n → ℕ)} {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}
    (hA : ∀ α ∈ A, mabs α ≤ m) (ha : ∀ α ∈ A, AnalyticOn ℝ (a α) Ω)
    (hell : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A a m x ξ ≠ 0)
    {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hDu : ∀ x ∈ Ω, diffOp A a u x = 0) {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) :
    AnalyticAt ℝ u x₀ := by
  classical
  have haAt : ∀ α ∈ A, AnalyticAt ℝ (a α) x₀ := fun α hα ↦
    (hΩ.analyticOn_iff_analyticOnNhd.1 (ha α hα)) x₀ hx₀
  obtain ⟨ρ, hρ, Ca0, Ma0, hCa0, hMa0, hcb⟩ := exists_coef_bound haAt
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  set R₁ := min ε ρ with hR₁
  have hR₁0 : 0 < R₁ := lt_min hε hρ

  obtain ⟨θ, hθ, hθc, _, hθs, hθ1⟩ := exists_cutoff x₀ hR₁0
  have hθC : ContDiff ℝ ∞ (fun y ↦ ((θ y : ℂ))) := Complex.ofRealCLM.contDiff.comp hθ
  have hθc' : HasCompactSupport (fun y ↦ ((θ y : ℂ))) :=
    hθc.comp_left (g := fun t : ℝ ↦ (t : ℂ)) Complex.ofReal_zero
  have hθΩ : tsupport (fun y ↦ ((θ y : ℂ))) ⊆ Ω :=
    (tsupport_comp_subset (g := fun t : ℝ ↦ (t : ℂ)) Complex.ofReal_zero θ).trans
      (hθs.trans ((Metric.ball_subset_ball (min_le_left _ _)).trans hεΩ))
  have haC : ∀ α ∈ A, ContDiffOn ℝ ∞ (a α) Ω := fun α hα ↦
    (ha α hα).contDiffOn hΩ.uniqueDiffOn
  set ã : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ := fun α y ↦ ((θ y : ℂ)) * a α y with hã
  set ũ : EuclideanSpace ℝ (Fin n) → ℂ := fun y ↦ ((θ y : ℂ)) * u y with hũ
  have hãC : ∀ α ∈ A, ContDiff ℝ ∞ (ã α) := fun α hα ↦
    contDiff_mul_of_tsupport hΩ (haC α hα) hθC hθΩ
  have hũC : ContDiff ℝ ∞ ũ := contDiff_mul_of_tsupport hΩ hu hθC hθΩ
  have hũc : HasCompactSupport ũ := hθc'.mul_right

  have hbnd : ∀ α ∈ A, ∃ C, ∀ x, ‖ã α x‖ ≤ C := fun α hα ↦
    (hãC α hα).continuous.bounded_above_of_compact_support hθc'.mul_right
  choose! Cb hCb using hbnd
  set A₀ : ℝ := ∑ α ∈ A, |Cb α| with hA₀def
  have hA₀0 : 0 ≤ A₀ := Finset.sum_nonneg fun α _ ↦ abs_nonneg _
  have hA₀ : ∀ α ∈ A, ∀ x, ‖ã α x‖ ≤ A₀ := fun α hα x ↦
    (hCb α hα x).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun β ↦ |Cb β|) (fun β _ ↦ abs_nonneg _) hα))

  set R₂ := R₁ / 2 with hR₂
  have hR₂0 : 0 < R₂ := by positivity
  have hev : ∀ y ∈ Metric.ball x₀ R₂, (∀ α, ã α =ᶠ[nhds y] a α) ∧ ũ =ᶠ[nhds y] u := by
    intro y hy
    have hnb : Metric.ball x₀ R₂ ∈ nhds y := Metric.isOpen_ball.mem_nhds hy
    refine ⟨fun α ↦ ?_, ?_⟩
    · filter_upwards [hnb] with z hz
      simp [hã, hθ1 z hz]
    · filter_upwards [hnb] with z hz
      simp [hũ, hθ1 z hz]
  have hR₂Ω : Metric.ball x₀ R₂ ⊆ Ω :=
    (Metric.ball_subset_ball (by
      have : R₁ ≤ ε := min_le_left _ _
      linarith)).trans hεΩ
  have hR₂ρ : Metric.ball x₀ R₂ ⊆ Metric.ball x₀ ρ :=
    Metric.ball_subset_ball (by
      have : R₁ ≤ ρ := min_le_right _ _
      linarith)
  have hPu : ∀ y ∈ Metric.ball x₀ R₂, diffOp A ã ũ y = 0 := by
    intro y hy
    rw [← hDu y (hR₂Ω hy)]
    simp only [diffOp]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [((hev y hy).1 α).eq_of_nhds, pderiv_eq_dT, pderiv_eq_dT,
      dT_congr_of_eventuallyEq (hev y hy).2]
  have hcoef : ∀ α ∈ A, ∀ y ∈ Metric.ball x₀ R₂, ∀ i,
      hsD i (ã α) y ≤ Ca0 * ((n : ℝ) * Ma0) ^ i * i.factorial := by
    intro α hα y hy i
    rw [hsD_congr_of_eventuallyEq ((hev y hy).1 α)]
    calc hsD i (a α) y ≤ (n : ℝ) ^ i * ‖iteratedFDeriv ℝ i (a α) y‖ :=
          hsD_le_norm_iteratedFDeriv i (a α) y
      _ ≤ (n : ℝ) ^ i * (Ca0 * Ma0 ^ i * i.factorial) := by
          gcongr; exact hcb α hα y (hR₂ρ hy) i
      _ = Ca0 * ((n : ℝ) * Ma0) ^ i * i.factorial := by ring

  have hx₀R₂ : x₀ ∈ Metric.ball x₀ R₂ := Metric.mem_ball_self hR₂0
  have hell0 : ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A ã m x₀ ξ ≠ 0 := by
    intro ξ hξ
    have e : prinSymbol A ã m x₀ ξ = prinSymbol A a m x₀ ξ := by
      simp only [prinSymbol, hã, hθ1 x₀ hx₀R₂, Complex.ofReal_one, one_mul]
    rw [e]
    exact hell x₀ hx₀ ξ hξ
  obtain ⟨R₀, hR₀, C₀, hC₀, hE⟩ :=
    elliptic_estimate (Or.inl hn) hA (fun α hα ↦ (hãC α hα).continuous) hell0

  set R := min R₂ R₀ with hR
  have hR0 : 0 < R := lt_min hR₂0 hR₀
  obtain ⟨χ, hχ, hχc, h01, hχs, hχ1⟩ := exists_cutoff x₀ hR0
  have hUR₂ : Metric.ball x₀ R ⊆ Metric.ball x₀ R₂ := Metric.ball_subset_ball (min_le_left _ _)
  have hUR₀ : Metric.ball x₀ R ⊆ Metric.ball x₀ R₀ := Metric.ball_subset_ball (min_le_right _ _)
  obtain ⟨σ, CS, hCS, hsob⟩ := sobolev_pointwise (n := n)
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_norm_iteratedFDeriv_pow_le hχ hχc h01 (m + σ)
  set K : ℝ := max 1 (n : ℝ) ^ (m + σ) * K₁ with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hK : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ m + σ → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i) := by
    intro s i x hi his
    have hni : (n : ℝ) ^ i ≤ max 1 (n : ℝ) ^ (m + σ) :=
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right _ _) i).trans
        (pow_le_pow_right₀ (le_max_left _ _) hi)
    have hb := hK₁ s i x hi his
    calc hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x
        ≤ (n : ℝ) ^ i * ‖iteratedFDeriv ℝ i (fun y ↦ ((χ y : ℂ)) ^ s) x‖ :=
          hsD_le_norm_iteratedFDeriv _ _ _
      _ ≤ max 1 (n : ℝ) ^ (m + σ) * (K₁ * (s : ℝ) ^ i * χ x ^ (s - i)) := by gcongr
      _ = K * (s : ℝ) ^ i * χ x ^ (s - i) := by rw [hKdef]; ring
  have hKm : ∀ (s i : ℕ) (x : EuclideanSpace ℝ (Fin n)), i ≤ m → i ≤ s →
      hsD i (fun y ↦ ((χ y : ℂ)) ^ s) x ≤ K * (s : ℝ) ^ i * χ x ^ (s - i) :=
    fun s i x hi his ↦ hK s i x (by omega) his
  have hE' : ∀ v : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ Metric.ball x₀ R → l2n (hsD m v) ≤
        C₀ * (l2n (fun x ↦ ‖diffOp A ã v x‖) + ∑ j ∈ range m, l2n (hsD j v)) :=
    fun v h1 h2 h3 ↦ hE v h1 h2 (h3.trans hUR₀)
  obtain ⟨B, L, hB, hL, hN⟩ := weighted_derivative_bound hm hãC hA₀0 hA₀ hA hũC hũc
    Metric.isOpen_ball (fun y hy ↦ hPu y (hUR₂ hy)) hχ h01 hχs hCa0
    (by positivity : (0 : ℝ) ≤ (n : ℝ) * Ma0) (fun α hα y hy i ↦ hcoef α hα y (hUR₂ hy) i)
    hC₀ hE' hK0 hKm
  obtain ⟨C, M, hbound⟩ := exists_norm_iteratedFDeriv_le_of_wN hũC hũc hχ h01 hK0 hK
    (σ := σ) (by omega) hCS hsob hB hL hN
  have hhalf : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ R₂ :=
    (Metric.ball_subset_ball (by linarith)).trans hUR₂
  refine analyticAt_of_norm_iteratedFDeriv_le (r := R / 2) (C := C) (M := M) (by positivity)
    (hu.mono (hhalf.trans hR₂Ω)) fun y hy k ↦ ?_
  rw [← (((hev y (hhalf hy)).2).iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  exact hbound k y (hχ1 y hy)

theorem analyticOn_of_elliptic {m : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    {A : Finset (Fin n → ℕ)} {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}
    (hA : ∀ α ∈ A, mabs α ≤ m) (ha : ∀ α ∈ A, AnalyticOn ℝ (a α) Ω)
    (hell : ∀ x ∈ Ω, ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A a m x ξ ≠ 0)
    {u : EuclideanSpace ℝ (Fin n) → ℂ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hDu : ∀ x ∈ Ω, diffOp A a u x = 0) : AnalyticOn ℝ u Ω := by
  intro x₀ hx₀
  refine AnalyticAt.analyticWithinAt ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  ·
    subst hn
    have hpt : ∀ y : EuclideanSpace ℝ (Fin 0), y = x₀ := fun y ↦ by
      ext i; exact Fin.elim0 i
    exact (analyticAt_const (v := u x₀)).congr
      (Filter.Eventually.of_forall fun y ↦ by rw [hpt y])
  rcases Nat.eq_zero_or_pos m with hm | hm
  ·
    subst hm
    have hA0 : ∀ α ∈ A, ∀ i, α i = 0 := fun α hα i ↦ by
      have h := hA α hα
      have h0 : mabs α = 0 := Nat.le_zero.1 h
      exact (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ _)
    have hzero : ∀ x ∈ Ω, u x = 0 := by
      intro x hx
      set ξ₀ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ 1
      have hξ₀ : ξ₀ ≠ 0 := by
        intro h
        have := congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ z ⟨0, hn⟩) h
        simp [ξ₀] at this
      have hs := hell x hx ξ₀ hξ₀
      have hmp : ∀ α ∈ A, mpow α ξ₀ = 1 := fun α hα ↦ by
        simp [mpow, hA0 α hα]
      have hfilt : A.filter (fun α ↦ mabs α = 0) = A :=
        Finset.filter_true_of_mem fun α hα ↦ Nat.le_zero.1 (hA α hα)
      have hsym : prinSymbol A a 0 x ξ₀ = ∑ α ∈ A, a α x := by
        simp only [prinSymbol, hfilt]
        exact Finset.sum_congr rfl fun α hα ↦ by rw [hmp α hα]; simp
      have hpd : ∀ α ∈ A, pderiv α u x = u x := by
        intro α hα
        have key : ∀ (j : ℕ), j = 0 → ∀ v : Fin j → EuclideanSpace ℝ (Fin n),
            iteratedFDeriv ℝ j u x v = u x := by
          rintro j rfl v
          simp
        exact key _ (Nat.le_zero.1 (hA α hα)) _
      have hD := hDu x hx
      simp only [diffOp] at hD
      rw [Finset.sum_congr rfl fun α hα ↦ by rw [hpd α hα], ← Finset.sum_mul] at hD
      rw [hsym] at hs
      exact (mul_eq_zero.1 hD).resolve_left hs
    refine (analyticAt_const (v := (0 : ℂ))).congr ?_
    filter_upwards [hΩ.mem_nhds hx₀] with y hy
    exact (hzero y hy).symm
  exact analyticAt_of_elliptic_of_pos hn hm hΩ hA ha hell hu hDu hx₀

end

end GroundTheory.Automorphic.Sobolev
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoelliptic =====
