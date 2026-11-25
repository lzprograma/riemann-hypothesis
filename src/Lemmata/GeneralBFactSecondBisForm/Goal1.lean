module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

universe u_1 u_2

namespace Bl.general_b_fact_second_bis_form

theorem goal1 {E : Type u_1} {F : Type u_2} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {f : E → F} {y : E} {δ M : ℝ}
    (hδ : 0 < δ) (hf : DifferentiableOn ℂ f (Metric.ball y δ))
    (hM : ∀ z ∈ Metric.ball y δ, ‖f z‖ ≤ M) :
    ‖fderiv ℂ f y‖ ≤ M / δ := by
  refine ContinuousLinearMap.opNorm_le_of_unit_norm
    (div_nonneg ((norm_nonneg _).trans (hM y (Metric.mem_ball_self hδ))) hδ.le) fun v hv => ?_
  let g := fun t : ℂ => y + t • v
  have hg (t : ℂ) : HasDerivAt g v t := by
    simpa [g] using ((hasDerivAt_id t).smul_const v).const_add y
  have hmaps : Set.MapsTo g (Metric.ball 0 δ) (Metric.ball y δ) := fun t ht => by
    simpa [g, Metric.mem_ball, dist_eq_norm, norm_smul, hv] using ht
  rw [← ((hf.differentiableAt (Metric.ball_mem_nhds y hδ)).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : ℂ) (hg 0) (by simp [g])).deriv]
  apply ge_of_tendsto (continuousWithinAt_const.div (continuousWithinAt_id (s := Set.Iio δ)) hδ.ne')
  filter_upwards [Ioo_mem_nhdsLT hδ] with r hr
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr.1
    ((hf.comp (fun t _ => (hg t).differentiableAt.differentiableWithinAt) hmaps).diffContOnCl_ball
      (Metric.closedBall_subset_ball hr.2))
    (fun t ht => hM _ (hmaps (Metric.sphere_subset_ball hr.2 ht)))

end Bl.general_b_fact_second_bis_form
