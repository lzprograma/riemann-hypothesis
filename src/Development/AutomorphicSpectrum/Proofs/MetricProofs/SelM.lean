module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Matrix.Defs

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

def selM {N : ℕ} (S : Finset (Fin N)) : Matrix (Fin N) (Fin S.card) ℂ :=
  Matrix.of fun a b => if a = S.orderEmbOfFin rfl b then 1 else 0

end GlobalTheory.CompanionTheory.Ar.PB.StepW
