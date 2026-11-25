module

import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinSt
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

theorem shortDual_holds : ShortDualStatement := by
  intro d L R μ hd hL hR hμ hmin δ hδ
  obtain ⟨e, he⟩ : ∃ e : (Fin d → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d), ∀ a, (e a).ofLp = a :=
    ⟨(WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm,
      fun a => (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).apply_symm_apply a⟩
  have hin : ∀ a b : Fin d → ℝ, inner ℝ (e a) (e b) = a ⬝ᵥ b := by
    intro a b
    rw [EuclideanSpace.inner_eq_star_dotProduct, he, he, dotProduct_comm]
    congr 1
  have hnorm : ∀ a : Fin d → ℝ, ‖e a‖ ^ 2 = a ⬝ᵥ a := by
    intro a
    rw [← real_inner_self_eq_norm_sq, hin]
  have hRR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hR
  classical
  let A : (Fin d → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    (R.toLinearEquiv' (Matrix.invertibleOfIsUnitDet R hR)).trans e
  have hA (x : Fin d → ℝ) : A x = e (R *ᵥ x) := rfl
  let bR := Pi.basisFun ℝ (Fin d)
  let bE := bR.map A
  have hbE (i : Fin d) : bE i = e (R *ᵥ Pi.single i 1) := by
    rw [Module.Basis.map_apply, hA, show bR i = Pi.single i 1 from Pi.basisFun_apply ℝ (Fin d) i]
  let M : Submodule ℤ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℤ (Set.range bE)
  have hspan : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin d))) = ⊤ := by
    rw [Submodule.span_span_of_tower, bE.span_eq]
  have hdisc : DiscreteTopology M := inferInstance
  have hsum (t : Fin d → ℤ) : (∑ i, t i • bE i) = e (R *ᵥ fun i => (t i : ℝ)) := by
    calc
      _ = A (∑ i, (t i : ℝ) • bR i) := by
        simp only [bE, Module.Basis.map_apply, map_sum, Int.cast_smul_eq_zsmul, map_zsmul]
      _ = _ := by
        rw [← hA, ← bR.sum_repr (fun i => (t i : ℝ))]
        rfl
  have hquad (t : Fin d → ℝ) : ‖e (R *ᵥ t)‖ ^ 2 = t ⬝ᵥ (L *ᵥ t) := by
    rw [hnorm, hL, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec t, Matrix.vecMul_transpose]
  have hlow : ∀ x ∈ M, x ≠ 0 → μ ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    have ht : t ≠ 0 := fun h => hx0 (by simp [h])
    rw [hsum]
    have hb := hmin t ht
    rw [← hquad] at hb
    nlinarith [norm_nonneg (e (R *ᵥ fun i => (t i : ℝ)))]
  have hMne : M ≠ ⊥ := (Submodule.ne_bot_iff _).mpr
    ⟨bE ⟨0, hd⟩, Submodule.subset_span (Set.mem_range_self _), bE.ne_zero _⟩
  have hminEq (P : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (i : ℕ) :
      PI.succMin P i = GlobalTheory.succMin P i := by
    unfold PI.succMin GlobalTheory.succMin GlobalTheory.succMinOf
    congr 1
    ext t
    rw [GlobalTheory.mem_succMinRadii_iff]
    exact and_congr_right (fun _ => ⟨
      fun ⟨v, hP, hli, hn⟩ => ⟨v, hli, fun j => ⟨hP j, hn j⟩⟩,
      fun ⟨v, hli, h⟩ => ⟨v, fun j => (h j).1, hli, fun j => (h j).2⟩⟩)
  have hdualEq : PI.dualZ M = GlobalTheory.dualLattice M := by
    ext y
    rw [GlobalTheory.mem_dualLattice]
    exact ⟨fun h x hx => (h x hx).imp (fun _ hz => ((real_inner_comm y x).trans hz).symm),
      fun h x hx => (h x hx).imp (fun _ hz => (real_inner_comm x y).trans hz.symm)⟩
  have hT := transference_successive_minima d M hdisc hspan 1 le_rfl hd
  rw [Nat.add_sub_cancel, hdualEq, hminEq, hminEq] at hT
  have hS1 : μ ≤ GlobalTheory.succMin M 1 := GlobalTheory.le_minNorm hMne hlow
  have hS2 : GlobalTheory.succMin (GlobalTheory.dualLattice M) d ≤ d / μ := by
    rw [le_div_iff₀ hμ]
    simpa only [mul_comm μ] using (mul_le_mul_of_nonneg_right hS1 (GlobalTheory.succMin_nonneg _ _)).trans hT
  let bD := GlobalTheory.innerDualBasis bE
  have hD : GlobalTheory.dualLattice M = Submodule.span ℤ (Set.range bD) :=
    GlobalTheory.dualLattice_span_basis bE
  letI : DiscreteTopology (GlobalTheory.dualLattice M) := by
    rw [hD]
    infer_instance
  have hdD : d ≤ Module.finrank ℝ (Submodule.span ℝ (GlobalTheory.dualLattice M : Set (EuclideanSpace ℝ (Fin d)))) := by
    rw [hD, Submodule.span_span_of_tower, bD.span_eq, finrank_top]
    simp
  obtain ⟨v, hvli, hv⟩ := GlobalTheory.exists_linearIndependent_norm_le_succMin hdD
  have hex (j : Fin d) : ∃ c : Fin d → ℤ, ∑ i, c i • bD i = v j :=
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hD ▸ (hv j).1)
  choose c hc using hex
  let g : (Fin d → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin d) :=
    ∑ i, LinearMap.smulRight (LinearMap.proj i) (bD i)
  have hg (t : Fin d → ℤ) : g t = ∑ i, t i • bD i := by
    simp [g, LinearMap.sum_apply]
  refine ⟨c, LinearIndependent.of_comp g ?_, fun j => ?_⟩
  · have heq : g ∘ c = v := funext fun j => (hg (c j)).trans (hc j)
    rw [heq]
    exact hvli.restrict_scalars (fun a b hab => by simpa using hab)
  · have hvj : v j = e ((fun i => (c j i : ℝ)) ᵥ* R⁻¹) := by
      refine InnerProductSpace.ext_inner_right_basis bE fun i => ?_
      rw [← hc j, sum_inner]
      conv_rhs =>
        rw [hbE i, hin, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hRR,
          Matrix.vecMul_one, dotProduct_single, mul_one]
      simp [bD, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, GlobalTheory.inner_innerDualBasis]
    rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose, ← hnorm, ← hvj]
    have hj := (hv j).2.trans hS2
    nlinarith [norm_nonneg (v j), div_nonneg (Nat.cast_nonneg d) hμ.le]


end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
