module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

namespace ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall

open MeasureTheory

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sqBall (r : ℕ) (E : Type*) [NormedAddCommGroup E] (R : ℝ) : Set (Fin r → E) :=
  {u | ∑ k, ‖u k‖ ^ 2 ≤ R ^ 2}

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace V] [BorelSpace V]

end Generic

end ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
