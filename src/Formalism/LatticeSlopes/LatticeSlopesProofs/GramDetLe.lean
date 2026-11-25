module

public import Formalism.LatticeSlopes.Statement
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open Module

noncomputable section

namespace Formalism.F

theorem normDet_le_pow_finrank {R F : Type*} [NormedAddCommGroup R] [InnerProductSpace ℝ R]
    [FiniteDimensional ℝ R] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : R →ₗ[ℝ] F) (K : ℝ) (hK : 0 ≤ K) (hg : ∀ y, ‖g y‖ ≤ K * ‖y‖) :
    g.normDet ≤ K ^ finrank ℝ R := by
  let T : R →ₗ[ℝ] LinearMap.range g := g.rangeRestrict
  have hT : g.normDet = T.normDet := (LinearMap.normDet_codRestrict (f := g) _).symm
  rw [hT, T.normDet_eq_prod_singularValues]
  calc ∏ i ∈ Finset.range (finrank ℝ R), T.singularValues i
      ≤ ∏ _i ∈ Finset.range (finrank ℝ R), K := by
        refine Finset.prod_le_prod₀ (fun i _ => T.singularValues_nonneg i) fun i hi => ?_
        obtain ⟨v, hv⟩ := (T.hasEigenvalue_adjoint_comp_self_sq_singularValues
          (Finset.mem_range.mp hi)).exists_hasEigenvector
        have hsq : T.singularValues i ^ 2 * ‖v‖ ^ 2 ≤ K ^ 2 * ‖v‖ ^ 2 := by
          have h1 : inner ℝ v ((LinearMap.adjoint T ∘ₗ T) v) = T.singularValues i ^ 2 * ‖v‖ ^ 2 := by
            simp [hv.apply_eq_smul, real_inner_smul_right]
          have h2 : inner ℝ v ((LinearMap.adjoint T ∘ₗ T) v) = ‖g v‖ ^ 2 := by
            rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
            rfl
          rw [← h1, h2, ← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hg v) 2
        have hv0 : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv.2)
        exact le_of_sq_le_sq (le_of_mul_le_mul_right hsq hv0) hK
    _ = K ^ finrank ℝ R := by simp

def linearCombinationMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (v : ι → E) : EuclideanSpace ℝ ι →ₗ[ℝ] E where
  toFun c := ∑ i, c i • v i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_smul]

theorem linearCombinationMap_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (v : ι → E) (c : EuclideanSpace ℝ ι) :
    linearCombinationMap v c = ∑ i, c i • v i := rfl

theorem det_gram_eq_normDet_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → E) :
    (Matrix.gram ℝ v).det = (linearCombinationMap v).normDet ^ 2 := by
  have hv : (fun i => linearCombinationMap v (EuclideanSpace.basisFun ι ℝ i)) = v := by
    funext i
    simp [linearCombinationMap_apply, EuclideanSpace.basisFun_apply]
  have h := (linearCombinationMap v).normDet_sq_eq_det_gram (EuclideanSpace.basisFun ι ℝ)
  rw [hv] at h
  exact h.symm

theorem gram_det_le : GramDetLe := by
  intro E F _ _ _ _ ι _ _ v w C hC
  have hvw : ∀ c : EuclideanSpace ℝ ι,
      ‖linearCombinationMap w c‖ ≤ C * ‖linearCombinationMap v c‖ := fun c => by
    simpa only [linearCombinationMap_apply] using hC (fun i => c i)
  rw [det_gram_eq_normDet_sq w, det_gram_eq_normDet_sq v]
  by_cases hinj : Function.Injective (linearCombinationMap v)
  · rcases isEmpty_or_nonempty ι with _ | hι
    · simp [LinearMap.normDet_of_subsingleton]
    obtain ⟨i⟩ := hι
    have hC0 : 0 ≤ C := by
      have hv0 : 0 < ‖linearCombinationMap v (EuclideanSpace.single i 1)‖ :=
        norm_pos_iff.mpr fun h => by
          have := congrArg (fun x : EuclideanSpace ℝ ι => x i) (hinj (h.trans (map_zero _).symm))
          simp at this
      exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hvw _)) hv0
    let e := LinearEquiv.ofInjective (linearCombinationMap v) hinj
    let G : LinearMap.range (linearCombinationMap v) →ₗ[ℝ] F :=
      linearCombinationMap w ∘ₗ e.symm.toLinearMap
    have hcomp : G ∘ₗ (linearCombinationMap v).rangeRestrict = linearCombinationMap w := by
      ext c
      exact congrArg (linearCombinationMap w) (e.symm_apply_apply c)
    have hG : ∀ y : LinearMap.range (linearCombinationMap v), ‖G y‖ ≤ C * ‖y‖ := fun y => by
      have hy : linearCombinationMap v (e.symm y) = y := congrArg Subtype.val (e.apply_symm_apply y)
      simpa [G, hy] using hvw (e.symm y)
    have hdom := normDet_le_pow_finrank G C hC0 hG
    rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace] at hdom
    have hle : (linearCombinationMap w).normDet ≤
        C ^ Fintype.card ι * (linearCombinationMap v).normDet := by
      have h1 : (G ∘ₗ (linearCombinationMap v).rangeRestrict).normDet =
          G.normDet * (linearCombinationMap v).rangeRestrict.normDet :=
        LinearMap.normDet_comp_of_finrank_eq _ _ (LinearMap.finrank_range_of_inj hinj).symm
      rw [← hcomp, h1, LinearMap.normDet_codRestrict]
      exact mul_le_mul_of_nonneg_right hdom (LinearMap.normDet_nonneg _)
    calc (linearCombinationMap w).normDet ^ 2
        ≤ (C ^ Fintype.card ι * (linearCombinationMap v).normDet) ^ 2 :=
          pow_le_pow_left₀ (LinearMap.normDet_nonneg _) hle 2
      _ = C ^ (2 * Fintype.card ι) * (linearCombinationMap v).normDet ^ 2 := by ring
  · rw [← LinearMap.ker_eq_bot] at hinj
    obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hinj
    have hkerW : (linearCombinationMap w).ker ≠ ⊥ := by
      refine (Submodule.ne_bot_iff _).2 ⟨c, ?_, hc0⟩
      rw [LinearMap.mem_ker, ← norm_le_zero_iff]
      simpa [LinearMap.mem_ker.1 hc] using hvw c
    rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hkerW, zero_pow two_ne_zero]
    rw [pow_mul]
    positivity

end Formalism.F
