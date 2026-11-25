module

public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

namespace Bl.DetMonotoneStarMulSelf

open Matrix
open scoped ComplexOrder MatrixOrder

private theorem one_le_re_det_one_add {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.PosSemidef) :
    1 ≤ (1 + D).det.re := by
  have hH := isHermitian_one.add hD.isHermitian
  rw [hH.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
  change 1 ≤ ∏ i, hH.eigenvalues i
  refine Finset.one_le_prod₀ fun i _ => ?_
  rw [hH.eigenvalues_eq i, add_mulVec, one_mulVec, dotProduct_add, map_add]
  rw [dotProduct_comm (star _) _, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, hH.eigenvectorBasis.orthonormal.1 i]
  simpa using hD.re_dotProduct_nonneg (hH.eigenvectorBasis i)

theorem goal1 : ∀ (n : ℕ), ReciprocityTheory.L2DbarEstimates.DetMonoStatement n := by
  intro n A B hB hAB
  by_cases hdet : B.det = 0
  · simpa [hdet] using (Complex.nonneg_iff.mp (hB.add hAB).det_nonneg).1
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hAB.nonneg
  rw [star_eq_conjTranspose] at hX
  obtain ⟨hRe, hIm⟩ := Complex.nonneg_iff.mp hB.det_nonneg
  calc
    B.det.re ≤ ((1 + X * B⁻¹ * Xᴴ).det * B.det).re := by
      simpa [Complex.mul_re, ← hIm] using mul_le_mul_of_nonneg_right
        (one_le_re_det_one_add _ (hB.inv.mul_mul_conjTranspose_same X)) hRe
    _ = A.det.re := by
      rw [det_one_add_mul_comm, ← Matrix.mul_assoc, ← hX, ← det_mul, Matrix.add_mul,
        Matrix.one_mul, nonsing_inv_mul_cancel_right _ _ (isUnit_iff_ne_zero.mpr hdet)]
      simp

end Bl.DetMonotoneStarMulSelf
