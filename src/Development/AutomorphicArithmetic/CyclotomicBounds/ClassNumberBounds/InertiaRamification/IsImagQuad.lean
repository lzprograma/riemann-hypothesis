module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic

@[expose] public section

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ}

def IsImagQuad (ψ : DirichletCharacter ℂ N) (d : ℕ) : Prop :=
  ψ ^ 2 = 1 ∧ ψ.Odd ∧ ψ.conductor = d

end KStar.Ram
