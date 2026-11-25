module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open ValuativeRel OnePoint

namespace GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k]

def Stable (S : Submodule ℂ (OnePoint k → ℂ)) : Prop :=
  (∀ F ∈ S, ∀ a b : k, a ≠ 0 → ∀ F' : OnePoint k → ℂ, F' ∞ = F ∞ →
    (∀ x : k, F' x = F ((a * x + b : k) : OnePoint k)) → F' ∈ S) ∧
  ∀ F ∈ S, ∀ F' : OnePoint k → ℂ, F' ∞ = F ((0 : k) : OnePoint k) → F' ((0 : k) : OnePoint k) = F ∞ →
    (∀ x : k, x ≠ 0 → F' x = F ((x⁻¹ : k) : OnePoint k)) → F' ∈ S



variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.LocGL.ProjLine
