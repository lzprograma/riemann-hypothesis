module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

open Finset Matrix

namespace Bl.general_b_fact

theorem goal1 {R : Type*} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R)
    (B : Matrix (Fin N) (Fin i) R) :
    (A * B).det = ∑ f : Fin i → Fin N, (∏ a, A a (f a)) * (B.submatrix f id).det := by
  classical
  have h1 : (A * B : Matrix (Fin i) (Fin i) R) = fun a => ∑ k, A a k • B k := by
    funext a j
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (detRowAlternating : (Fin i → R) [⋀^Fin i]→ₗ[R] R).toMultilinearMap (A * B) = _
  rw [h1, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

end Bl.general_b_fact
