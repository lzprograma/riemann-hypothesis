module

public import Formalism.GelfandTransference.Statement
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section

namespace Bl.DetNormLeProdRows

/-- The Gram–Schmidt basis makes the row coordinate matrix triangular. Changing between
orthonormal bases preserves the modulus of the determinant, and Cauchy–Schwarz bounds each
diagonal entry in modulus by the norm of its row in the original matrix. -/
private theorem det_norm_le_prod_rows (ρ : ℕ) (A : Matrix (Fin ρ) (Fin ρ) ℂ) :
    ‖A.det‖ ≤ ∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin ρ))‖ := by
  classical
  let v : Fin ρ → EuclideanSpace ℂ (Fin ρ) := fun i => WithLp.toLp 2 (A i)
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin ρ)) = Fintype.card (Fin ρ) := by simp
  let e := (EuclideanSpace.basisFun (Fin ρ) ℂ).toBasis
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h v
  have he : e.det v = A.det := by rw [Module.Basis.det_apply, ← Matrix.det_transpose A]; congr 1
  have hbv : b.toBasis.det v = b.toBasis.det e * e.det v := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_mul,
      Module.Basis.toMatrix_mul_toMatrix]
  have key : ‖A.det‖ = ‖b.toBasis.det v‖ := by
    rw [hbv, norm_mul, show ‖b.toBasis.det e‖ = 1 by simp [e], one_mul, he]
  rw [key, InnerProductSpace.gramSchmidtOrthonormalBasis_det h v, norm_prod]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => ?_
  calc ‖inner ℂ (b i) (v i)‖ ≤ ‖b i‖ * ‖v i‖ := norm_inner_le_norm _ _
    _ = ‖v i‖ := by rw [b.orthonormal.1 i, one_mul]

/-- Hadamard's determinant inequality in squared form: the squared modulus of the determinant
of a complex matrix is at most the product of the squared Euclidean norms of its rows.

See [Hadamard (1893), §4, p. 242](https://zenodo.org/records/18674602).
-/
theorem goal1 : Formalism.HadamardInequality.Hadamard := fun ρ A =>
  calc ‖A.det‖ ^ 2 ≤ (∏ i, ‖(WithLp.toLp 2 (A i) : EuclideanSpace ℂ (Fin ρ))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (det_norm_le_prod_rows ρ A) 2
    _ = ∏ i, ∑ j, ‖A i j‖ ^ 2 := by
        rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun i _ => EuclideanSpace.norm_sq_eq _

end Bl.DetNormLeProdRows
