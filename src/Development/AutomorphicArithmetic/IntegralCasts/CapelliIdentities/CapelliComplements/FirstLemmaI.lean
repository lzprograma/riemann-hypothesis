module

public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

universe u_1

namespace Bl.MatrixMapSub

theorem goal1 {A : Type u_1} [CommRing A] {d : ℕ} (σ : A →+* A)
    (X Y : Matrix (Fin d) (Fin d) A) :
    (X - Y).map σ = X.map σ - Y.map σ := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]

end Bl.MatrixMapSub
