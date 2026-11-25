module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Ultra.Basic

@[expose] public section

noncomputable section

namespace CompanionTheory.Rg.FlB

section Defs

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]

def IsHerm (s : L →+* L) (h : V → V → L) : Prop :=
  (∀ x y z, h x (y + z) = h x y + h x z) ∧ (∀ (a : L) x y, h x (a • y) = a * h x y) ∧ (∀ x y, h y x = s (h x y)) ∧
    ∀ x, (∀ y, h x y = 0) → x = 0

end Defs

end CompanionTheory.Rg.FlB

end
