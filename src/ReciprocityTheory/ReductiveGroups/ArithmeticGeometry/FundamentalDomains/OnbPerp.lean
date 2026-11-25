module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis

open Complex
open scoped ComplexConjugate InnerProductSpace

theorem onb_perp (n : ℕ) (hn : 1 ≤ n) (α : Fin n → ℂ) (hα : α ≠ 0) :
    ∃ g : Fin (n - 1) → Fin n → ℂ,
      (∀ k l, ∑ a, g k a * conj (g l a) = if k = l then 1 else 0) ∧
      (∀ k, ∑ a, g k a * conj (α a) = 0) ∧
      (∀ γ : Fin n → ℂ, ∑ a, γ a * conj (α a) = 0 → γ ∈ Submodule.span ℂ (Set.range g)) := by
  classical
  let v : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 α
  have hv : v ≠ 0 := by simpa [v] using hα
  have : Fact (Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = (n - 1) + 1) :=
    ⟨by rw [finrank_euclideanSpace_fin, Nat.sub_add_cancel hn]⟩
  let b : OrthonormalBasis (Fin (n - 1)) ℂ (ℂ ∙ v)ᗮ :=
    OrthonormalBasis.fromOrthogonalSpanSingleton (n - 1) hv
  refine ⟨fun k a => ((b k : (ℂ ∙ v)ᗮ) : EuclideanSpace ℂ (Fin n)).ofLp a, ?_, ?_, ?_⟩
  · intro k l
    have h := (orthonormal_iff_ite.mp b.orthonormal) l k
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct] at h
    simp only [dotProduct, Pi.star_apply, RCLike.star_def] at h
    rw [h]
    exact if_congr eq_comm rfl rfl
  · intro k
    have h := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (b k).2
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa [dotProduct, v] using h
  · intro γ hγ
    have hw : (WithLp.toLp 2 γ : EuclideanSpace ℂ (Fin n)) ∈ (ℂ ∙ v)ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, EuclideanSpace.inner_eq_star_dotProduct]
      simpa [dotProduct, v] using hγ
    simpa only [← Set.range_comp, Function.comp_def, LinearMap.comp_apply,
      LinearEquiv.coe_coe, WithLp.coe_linearEquiv, Submodule.subtype_apply,
      WithLp.ofLp_toLp] using
      Submodule.apply_mem_span_image_of_mem_span
        ((WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap.comp (ℂ ∙ v)ᗮ.subtype)
        (show (⟨_, hw⟩ : (ℂ ∙ v)ᗮ) ∈ Submodule.span ℂ (Set.range b) by
          rw [← b.coe_toBasis, b.toBasis.span_eq]
          exact Submodule.mem_top)

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalPerpBasis
