module

public import GroundTheory.AutomorphicForms.HilbertSchmidt
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace GroundTheory.Automorphic

open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap Filter Topology

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]

def hsTruncation {ι : Type*} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) (F : Finset ι) :
    H →L[𝕜] K :=
  ∑ i ∈ F, (innerSL 𝕜 (b i)).smulRight (T (b i))

omit [CompleteSpace H] [CompleteSpace K] in
theorem isCompactOperator_hsTruncation {ι : Type*} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K)
    (F : Finset ι) : IsCompactOperator (hsTruncation b T F) := by
  exact (compactOperator (RingHom.id 𝕜) H K).sum_mem fun i _ =>
    (isCompactOperator_of_locallyCompactSpace_dom (innerSL 𝕜 (b i))).continuous_comp
      (continuous_id.smul continuous_const)

omit [CompleteSpace H] [CompleteSpace K] in
theorem sub_hsTruncation_apply_basis {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι 𝕜 H)
    (T : H →L[𝕜] K) (F : Finset ι) (j : ι) :
    (T - hsTruncation b T F) (b j) = if j ∈ F then 0 else T (b j) := by
  have hb : ∀ i, ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 := fun i =>
    orthonormal_iff_ite.mp b.orthonormal i j
  simp only [sub_apply, hsTruncation, FunLike.coe_sum, Finset.sum_apply, smulRight_apply,
    innerSL_apply_apply, hb, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq']
  split_ifs <;> simp


omit [CompleteSpace K] in
theorem hsNormSq_sub_hsTruncation (T : H →L[𝕜] K) (F : Finset (exists_hilbertBasis 𝕜 H).choose) :
    hsNormSq (T - hsTruncation (stdHilbertBasis (𝕜 := 𝕜) (H := H)) T F) =
      ∑' i : {i // i ∉ F}, ‖T (stdHilbertBasis (𝕜 := 𝕜) (H := H) i)‖ₑ ^ 2 := by
  classical
  rw [hsNormSq]
  refine Eq.trans ?_ (tsum_subtype {i | i ∉ F}
    (fun i => ‖T (stdHilbertBasis (𝕜 := 𝕜) (H := H) i)‖ₑ ^ 2)).symm
  refine tsum_congr fun j => ?_
  rw [sub_hsTruncation_apply_basis]
  by_cases hj : j ∈ F
  · simp [hj]
  · simp [hj]

theorem IsHilbertSchmidt.isCompactOperator {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) :
    IsCompactOperator T := by
  set b := stdHilbertBasis (𝕜 := 𝕜) (H := H)
  have htail : Tendsto (fun F : Finset (exists_hilbertBasis 𝕜 H).choose =>
      hsNormSq (T - hsTruncation b T F)) atTop (𝓝 0) := by
    simp only [b, hsNormSq_sub_hsTruncation]
    exact ENNReal.tendsto_tsum_compl_atTop_zero hT.ne
  have hHS : ∀ F, IsHilbertSchmidt (T - hsTruncation b T F) := fun F => by
    refine lt_of_le_of_lt ?_ hT
    rw [hsNormSq_sub_hsTruncation, hsNormSq]
    exact tsum_comp_le_tsum_of_injective Subtype.val_injective (fun i => ‖T (b i)‖ₑ ^ 2)
  have hnorm : Tendsto (fun F => hsNorm (T - hsTruncation b T F)) atTop (𝓝 0) := by
    have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htail
    have h2 := (Real.continuous_sqrt.tendsto _).comp h1
    simpa [hsNorm, Function.comp_def] using h2
  refine isCompactOperator_of_tendsto (l := atTop) (F := fun F => hsTruncation b T F) ?_
    (Eventually.of_forall fun F => isCompactOperator_hsTruncation b T F)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun F => ?_) hnorm
  rw [norm_sub_rev]
  exact norm_le_hsNorm (hHS F)

end

end GroundTheory.Automorphic
