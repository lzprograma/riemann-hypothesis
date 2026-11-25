module
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2

@[expose] public section
open MeasureTheory
open scoped ContDiff Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.CutSH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_derivative : CutSH.FamDeriv := by
  rintro Wp Wq _ _ _ _ _ _ P T j G ⟨hloc, hsupp⟩ v
  constructor
  · intro t₀ ht₀ γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hGf⟩ := hloc t₀ ht₀ γ₀ hγ₀
    refine ⟨U, fun p => fderiv ℝ f p ((v, 0) : ℂ × B.Mat P.k (P.r - (j + 1))), hU, hmem,
      (hf.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const, ?_⟩
    rintro ⟨t, γ⟩ hp hγ
    simp only [famP, Set.indicator_of_mem hγ, (show (fun u : ℂ => G u γ) =ᶠ[𝓝 t] fun u => f (u, γ) by
      filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (hU.mem_nhds hp)] with u hu using hGf (u, γ) hu hγ).fderiv_eq]
    exact congrArg (fun L : ℂ →L[ℝ] _ => L v)
      ((((hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)).hasFDerivAt.comp t
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) t γ)).fderiv)
  · intro K hK hK0
    obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open (isOpen_compl_singleton (x := (0 : ℂ)))
      (fun t ht => by simpa using hK0 t ht)
    obtain ⟨C, hC, ε, hε, hCε⟩ := hsupp (Metric.cthickening δ K) hK.cthickening
      (fun t ht => by simpa using hsub ht)
    refine ⟨C, hC, ε, hε, fun t ht γ hne => ?_⟩
    have hγ : γ ∈ B.GV P.k (P.r - (j + 1)) :=
      Classical.byContradiction fun h => hne (by simp [famP, Set.indicator_of_notMem h])
    obtain ⟨u, hu, hGu⟩ : ∃ u ∈ Metric.ball t δ, G u γ ≠ 0 := by
      by_contra! h
      exact hne (by simp [famP, Set.indicator_of_mem hγ, (show (fun u : ℂ => G u γ) =ᶠ[𝓝 t] fun _ => 0 by
        filter_upwards [Metric.ball_mem_nhds t hδ] with u hu using h u hu).fderiv_eq])
    obtain ⟨hγC, hε'⟩ := hCε u
      (Metric.mem_cthickening_of_dist_le u t δ K ht (Metric.mem_ball.mp hu).le) γ hGu
    exact ⟨hγC, fun _ => hε' hγ⟩

end Formalism.FourierDecayAlt.P
