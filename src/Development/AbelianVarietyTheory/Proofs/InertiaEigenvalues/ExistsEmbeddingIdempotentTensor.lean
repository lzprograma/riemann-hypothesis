module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.RingTheory.Trace.Basic

@[expose] public section

open TensorProduct

namespace GlobalTheory


open TensorProduct in
theorem _root_.GlobalTheory.exists_embedding_idempotent_tensor (F K L : Type) [Field F] [CharZero F] [Field K]
    [Field L] [Algebra F K] [Algebra F L] [FiniteDimensional F K] (τ : K →ₐ[F] L) :
    ∃ (m : ℕ) (c : Fin m → L) (k : Fin m → K), ∑ j, c j * τ (k j) = 1 ∧
      ∀ y : K, ∑ j, c j ⊗ₜ[F] (y * k j) = ∑ j, (τ y * c j) ⊗ₜ[F] k j := by
  classical
  have hB : (Algebra.traceForm F K).Nondegenerate := traceForm_nondegenerate F K
  have hsymm : (Algebra.traceForm F K).IsSymm := Algebra.traceForm_isSymm F
  let b := Module.finBasis F K
  let d := (Algebra.traceForm F K).dualBasis hB b
  have hbd : ∀ i j, Algebra.trace F K (b i * d j) = if i = j then 1 else 0 := fun i j => by
    rw [← Algebra.traceForm_apply]
    exact LinearMap.BilinForm.apply_dualBasis_right hB hsymm b i j
  set s : K := ∑ j, b j * d j with hs
  have hdual : ∀ (b' : Module.Basis (Fin (Module.finrank F K)) F K) (x : K),
      ∑ i, Algebra.trace F K (x * b' i) • (Algebra.traceForm F K).dualBasis hB b' i = x := by
    intro b' x
    conv_rhs => rw [← Module.Basis.sum_repr ((Algebra.traceForm F K).dualBasis hB b') x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  have hd : ∀ x : K, ∑ i, Algebra.trace F K (x * b i) • d i = x := hdual b
  have hb : ∀ x : K, ∑ j, Algebra.trace F K (x * d j) • b j = x := fun x => by
    rw [← LinearMap.BilinForm.dualBasis_dualBasis hB hsymm b]
    exact hdual d x
  have htr : Algebra.trace F K s = (Module.finrank F K : F) := by
    simp [hs, hbd]
  have hs0 : s ≠ 0 := fun h =>
    (Module.finrank_pos (R := F) (M := K)).ne' (Nat.cast_eq_zero.mp (by rw [← htr, h, map_zero]))
  refine ⟨Module.finrank F K, fun j => τ (s⁻¹ * b j), d, ?_, fun y => ?_⟩
  · calc ∑ j, τ (s⁻¹ * b j) * τ (d j) = τ (s⁻¹ * s) := by
          simp only [← map_mul, ← map_sum, hs, Finset.mul_sum, mul_assoc]
      _ = 1 := by rw [inv_mul_cancel₀ hs0, map_one]
  · have lhs : ∑ j, τ (s⁻¹ * b j) ⊗ₜ[F] (y * d j) =
        ∑ j, ∑ i, (Algebra.trace F K (y * d j * b i) • τ (s⁻¹ * b j)) ⊗ₜ[F] d i := by
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [← hd (y * d j)]
      simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have rhs : ∑ i, (τ y * τ (s⁻¹ * b i)) ⊗ₜ[F] d i =
        ∑ i, ∑ j, (Algebra.trace F K (y * b i * d j) • τ (s⁻¹ * b j)) ⊗ₜ[F] d i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← map_mul, mul_left_comm]
      conv_lhs => rw [← hb (y * b i)]
      simp only [Finset.mul_sum, map_sum, TensorProduct.sum_tmul, mul_smul_comm, map_smul]
    rw [lhs, rhs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_right_comm y (d j) (b i)]

end GlobalTheory
