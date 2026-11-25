module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Young.YoungDiagram

@[expose] public section

noncomputable section

namespace Formalism.LatticeIndexTer

def ph (u : ℝ) : ℝ := u * Real.log u - u

def Interlaced (k : ℕ) (c : Fin (k + 1) → ℝ) (c' : Fin k → ℝ) (S : ℝ) : Prop :=
  (∀ i, 0 ≤ c i ∧ c i ≤ S) ∧ ∀ i : Fin k, c' i ≤ c i.castSucc ∧ c i.succ ≤ c' i

def hookProd (μ : YoungDiagram) : ℕ :=
  ∏ x ∈ μ.cells, ((μ.rowLen x.1 - x.2) + (μ.colLen x.2 - x.1) - 1)

end Formalism.LatticeIndexTer
