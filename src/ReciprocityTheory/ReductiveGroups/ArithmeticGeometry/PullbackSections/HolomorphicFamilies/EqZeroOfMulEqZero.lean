module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Lemmata.FirstBlockLemmaJ.Imports
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open Metric Set Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem eq_zero_of_eventually {U : Set V} (hU : IsOpen U) (hc : IsPreconnected U) {g : V → ℂ}
    (hg : DifferentiableOn ℂ g U) {x0 : V} (hx0 : x0 ∈ U) (h0 : g =ᶠ[𝓝 x0] 0) : ∀ y ∈ U, g y = 0 := by
  have hZo : IsOpen {x : V | g =ᶠ[𝓝 x] 0} := isOpen_setOfPred_eventually_nhds
  have hsub : U ⊆ {x : V | g =ᶠ[𝓝 x] 0} := by
    refine hc.subset_of_closure_inter_subset hZo ⟨x0, hx0, h0⟩ ?_
    rintro x ⟨hxc, hxU⟩
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hU x hxU
    obtain ⟨z, hzZ, hzd⟩ := Metric.mem_closure_iff.mp hxc ε hε
    have hzb : z ∈ ball x ε := by rw [mem_ball, dist_comm]; exact hzd
    have hz0 : g =ᶠ[𝓝 z] 0 := hzZ
    have hgb : DifferentiableOn ℂ g (ball x ε) := hg.mono hb
    have hall : ∀ y ∈ ball x ε, g y = 0 := by
      intro y hy
      let ψ : ℂ →ₗ[ℂ] V := (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (y - z)
      let φ : ℂ →ᵃ[ℝ] V := AffineMap.const ℝ ℂ z + (ψ.restrictScalars ℝ).toAffineMap
      have hφ (t : ℂ) : φ t = z + t • (y - z) := rfl
      have hφd : Differentiable ℂ φ :=
        (differentiable_const z).add (differentiable_id.smul_const (y - z))
      let W : Set ℂ := φ ⁻¹' ball x ε
      have hWo : IsOpen W := isOpen_ball.preimage hφd.continuous
      have hWc : IsPreconnected W := ((convex_ball x ε).affine_preimage φ).isPreconnected
      have hdiff : DifferentiableOn ℂ (g ∘ φ) W := hgb.comp hφd.differentiableOn (fun _ ht => ht)
      have h0' : (0 : ℂ) ∈ W := by simpa [W, hφ] using hzb
      have h1' : (1 : ℂ) ∈ W := by simpa [W, hφ] using hy
      have ht : Tendsto φ (𝓝 0) (𝓝 z) := by
        simpa [hφ] using hφd.continuous.tendsto (0 : ℂ)
      have hev : (g ∘ φ) =ᶠ[𝓝 (0 : ℂ)] 0 :=
        (ht.eventually hz0).mono (fun _ h => by simpa using h)
      simpa [hφ] using
        (hdiff.analyticOnNhd hWo).eqOn_zero_of_preconnected_of_eventuallyEq_zero hWc h0' hev h1'
    exact Filter.eventually_of_mem (ball_mem_nhds x hε) hall
  intro y hy
  exact (hsub hy).self_of_nhds

theorem eq_zero_of_mul_eq_zero {U : Set V} (hU : IsOpen U) (hc : IsPreconnected U) {f g : V → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hfg : ∀ y ∈ U, f y * g y = 0)
    {x0 : V} (hx0 : x0 ∈ U) (h0 : f x0 ≠ 0) : ∀ y ∈ U, g y = 0 := by
  refine eq_zero_of_eventually hU hc hg hx0 ?_
  have h1 : ∀ᶠ y in 𝓝 x0, f y ≠ 0 := (hf.continuousOn.continuousAt (hU.mem_nhds hx0)).eventually_ne h0
  filter_upwards [h1, hU.mem_nhds hx0] with y hy hyU
  exact (mul_eq_zero.mp (hfg y hyU)).resolve_left hy

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
