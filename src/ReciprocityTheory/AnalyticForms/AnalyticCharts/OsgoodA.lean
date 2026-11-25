module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.TorusIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

noncomputable section

namespace ReciprocityTheory.AnForm.Osgood

open Complex Metric MeasureTheory Set Filter Topology

open scoped Real

theorem differentiable_cons_right {n : ℕ} (x : ℂ) :
    Differentiable ℂ (fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact differentiable_const x
  · simp only [Fin.cons_succ]
    exact differentiable_pi.1 differentiable_id j

theorem differentiable_cons_left {n : ℕ} (y : Fin n → ℂ) :
    Differentiable ℂ (fun x : ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact differentiable_id
  · simp only [Fin.cons_succ]
    exact differentiable_const _

theorem mem_closedBall_pi_iff {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r) :
    z ∈ closedBall c r ↔ ∀ i, z i ∈ closedBall (c i) r := by
  rw [closedBall_pi c hr, Set.mem_univ_pi]

theorem mem_ball_pi_iff {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) :
    z ∈ ball c r ↔ ∀ i, z i ∈ ball (c i) r := by
  rw [ball_pi c hr, Set.mem_univ_pi]

theorem norm_torusMap_sub {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin n → ℝ) (i : Fin n) :
    ‖torusMap c (fun _ => r) θ i - c i‖ = r := by
  have h : torusMap c (fun _ => r) θ i - c i = (r : ℂ) * exp ((θ i : ℂ) * I) := by
    simp only [torusMap]
    ring
  have h1 : ‖exp ((θ i : ℂ) * I)‖ = 1 := by
    exact Complex.norm_exp_ofReal_mul_I _
  have h2 : ‖(r : ℂ)‖ = r := by
    exact Complex.norm_of_nonneg hr
  rw [h, norm_mul, h1, h2, mul_one]

theorem torusMap_mem_closedBall {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin n → ℝ) :
    torusMap c (fun _ => r) θ ∈ closedBall c r := by
  refine (mem_closedBall_pi_iff hr).2 fun i => ?_
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_torusMap_sub c hr θ i).le

theorem torusMap_sub_ne {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r)
    (θ : Fin n → ℝ) (i : Fin n) : torusMap c (fun _ => r) θ i - z i ≠ 0 := by
  intro h
  have h1 := (mem_ball_pi_iff hr).1 hz i
  rw [mem_ball, dist_eq_norm] at h1
  have h2 := norm_torusMap_sub c hr.le θ i
  rw [sub_eq_zero] at h
  rw [h] at h2
  linarith

theorem continuous_torusMap {n : ℕ} (c : Fin n → ℂ) (r : ℝ) :
    Continuous (torusMap c (fun _ => r)) := by
  refine continuous_pi fun i => ?_
  simp only [torusMap]
  fun_prop

theorem continuous_comp_torusMap {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) :
    Continuous fun θ => f (torusMap c (fun _ => r) θ) := by
  refine continuous_iff_continuousAt.2 fun θ => ?_
  exact (hf _ (torusMap_mem_closedBall c hr θ)).continuousAt.comp
    (continuous_torusMap c r).continuousAt

theorem torusIntegrable_kernel {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) (hz : z ∈ ball c r) :
    TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * f ζ) c (fun _ => r) := by
  have hK : Continuous fun θ => ∏ i, (torusMap c (fun _ => r) θ i - z i)⁻¹ := by
    refine continuous_finsetProd Finset.univ fun i _ => ?_
    refine Continuous.inv₀ ?_ ?_
    · exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const
    · intro θ
      exact torusMap_sub_ne hr hz θ i
  have hcont : Continuous fun θ =>
      (∏ i, (torusMap c (fun _ => r) θ i - z i)⁻¹) * f (torusMap c (fun _ => r) θ) :=
    hK.mul (continuous_comp_torusMap hr.le hf)
  unfold TorusIntegrable
  exact hcont.continuousOn.integrableOn_compact isCompact_Icc

end ReciprocityTheory.AnForm.Osgood
