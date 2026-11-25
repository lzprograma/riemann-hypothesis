module
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section
universe u_1
namespace Bl.general_b_fact_bis_form

theorem goal1 {F : Type u_1} [NormedAddCommGroup F] [NormedSpace ℂ F] {U : Set F}
    (hU : IsOpen U) {G : F → ℂ} (hG : DifferentiableOn ℂ G U) {y : F} {R C : ℝ}
    (hR : 0 < R) (hsub : Metric.closedBall y R ⊆ U)
    (hC : ∀ z ∈ Metric.closedBall y R, ‖G z‖ ≤ C) :
    ‖fderiv ℂ G y‖ ≤ C / R := by
  have hy := Metric.mem_closedBall_self (x := y) hR.le
  refine ContinuousLinearMap.opNorm_le_of_unit_norm
    (div_nonneg ((norm_nonneg _).trans (hC y hy)) hR.le) fun v hv => ?_
  let line := fun t : ℂ => y + t • v
  have hd (t : ℂ) : HasDerivAt line v t := by
    simpa [line] using ((hasDerivAt_id t).smul_const v).const_add y
  have hm : Set.MapsTo line (Metric.closedBall 0 R) (Metric.closedBall y R) := fun t ht => by
    simpa [line, Metric.mem_closedBall, dist_eq_norm, norm_smul, hv] using ht
  rw [← ((hG.differentiableAt (hU.mem_nhds (hsub hy))).hasFDerivAt.comp_hasDerivAt_of_eq
    0 (hd 0) (by simp [line])).deriv]
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR ?_ fun t ht =>
    hC _ (hm (Metric.sphere_subset_closedBall ht))
  exact (hG.comp (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    (fun _ ht => hsub (hm ht))).diffContOnCl_ball Set.Subset.rfl
end Bl.general_b_fact_bis_form
