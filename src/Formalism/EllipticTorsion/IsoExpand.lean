module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Fintype.Basic

@[expose] public section

universe u

namespace Formalism.ELL

def quadDiff {M T : Type u} [AddCommGroup M] [AddCommGroup T] (φ : M → T) (a b : M) : T :=
  φ (a + b) - φ a - φ b

end Formalism.ELL
