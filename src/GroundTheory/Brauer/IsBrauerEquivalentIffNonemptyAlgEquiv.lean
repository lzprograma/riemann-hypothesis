module

public import Mathlib.Algebra.Azumaya.Defs
public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import GroundTheory.Brauer.TensorSimple
public import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Brauer

open TensorProduct

universe u v w

section Azumaya

variable {K : Type u} [Field K] {A : Type v} [Ring A] [Algebra K A]
  [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]


omit [FiniteDimensional K A] in
variable (K A) in
theorem mulLeftRight_injective : Function.Injective (AlgHom.mulLeftRight K A) :=
  RingHom.injective (AlgHom.mulLeftRight K A).toRingHom


variable (K A) in
theorem mulLeftRight_bijective : Function.Bijective (AlgHom.mulLeftRight K A) := by
  refine ⟨mulLeftRight_injective K A, ?_⟩
  have h := LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (AlgHom.mulLeftRight K A).toLinearMap)
    (by rw [Module.finrank_tensorProduct, MulOpposite.finrank, Module.finrank_linearMap])
  exact h.mp (mulLeftRight_injective K A)


end Azumaya

end GroundTheory.Brauer
