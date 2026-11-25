module

public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

universe u_1

namespace Bl.MatrixMapSmul

theorem goal1 {A : Type u_1} [CommRing A] {d : ℕ} (σ : A →+* A) (a : A)
    (X : Matrix (Fin d) (Fin d) A) :
    (a • X).map σ = σ a • X.map σ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

end Bl.MatrixMapSmul
