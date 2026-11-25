module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

namespace Formalism.NuclearRankWeightBounds.D

open Finset

noncomputable def lead {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : ℕ) : ℂ :=
  if hi : i ≤ N then (A.submatrix (Fin.castLE hi) (Fin.castLE hi)).det else 1

noncomputable def hs {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  Real.sqrt (∑ a, ∑ b, ‖Y a b‖ ^ 2)

def q0 {N : ℕ} (ep : Fin N → Bool) : ℕ :=
  min (univ.filter fun a => ep a = true).card (univ.filter fun a => ep a = false).card

end Formalism.NuclearRankWeightBounds.D
