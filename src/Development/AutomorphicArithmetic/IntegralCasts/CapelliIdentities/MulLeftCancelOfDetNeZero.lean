module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

theorem UpperTheory.Reformulated.B.Yoa2.mul_left_cancel_of_det_ne_zero.{u_1} :
    ∀ {R : Type u_1} [CommRing R] [IsDomain R] {n : ℕ} {A X Y : Matrix (Fin n) (Fin n) R},
      A.det ≠ (0 : R) → A * X = A * Y → X = Y := by
  intro R _ _ n A X Y hA h
  exact (Matrix.isRegular_of_isLeftRegular_det fun _ _ => mul_left_cancel₀ hA).left h
