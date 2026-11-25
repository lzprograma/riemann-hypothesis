module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

noncomputable section

open MvPolynomial Matrix
open scoped ContDiff

namespace PositivityTheory.RgTw

variable {n : ℕ}

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

abbrev G (n : ℕ) := Matrix.GeneralLinearGroup (Fin n) ℂ

def hb (p : Fin n × Fin n) : Mat n :=
  if p.1 = p.2 then Matrix.single p.1 p.1 1
  else if p.1 < p.2 then ((Real.sqrt 2)⁻¹ : ℂ) • (Matrix.single p.1 p.2 1 + Matrix.single p.2 p.1 1)
  else (((Real.sqrt 2)⁻¹ : ℂ) * Complex.I) • (Matrix.single p.1 p.2 1 - Matrix.single p.2 p.1 1)

def th (g : G n) : G n := (star g)⁻¹

theorem th_one : th (1 : G n) = 1 := by simp [th]

def tw (x d : G n) : G n := x⁻¹ * d * th x

end PositivityTheory.RgTw
