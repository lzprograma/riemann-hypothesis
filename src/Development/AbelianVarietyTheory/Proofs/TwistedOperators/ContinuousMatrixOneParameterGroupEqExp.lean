module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsUnitIntegral
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.TypeStar

@[expose] public section

open scoped Matrix
open Filter Topology

namespace GlobalTheory

theorem matrix_oneParamGroup_eq_exp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (M : ℝ → Matrix ι ι ℝ), Continuous M → M 0 = 1 → (∀ s t, M (s + t) = M s * M t) →
    ∃ X : Matrix ι ι ℝ, ∀ t, M t = NormedSpace.exp (t • X) := by
  intro ι _ _ M hc h0 hm
  letI : NormedRing (Matrix ι ι ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix ι ι ℝ) := Matrix.linftyOpNormedAlgebra
  obtain ⟨X, hX⟩ := _root_.GlobalTheory.ExponentialIntegralUnits.exists_exp_eq M hc h0 hm
  exact ⟨X, fun t => (hX t).symm⟩

end GlobalTheory
