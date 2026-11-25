module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.Idempotent

@[expose] public section

namespace GlobalTheory.PeirceDecompositionCut

variable {R : Type*} [CommRing R] (A : Type*) [Ring A] [Algebra R A]

def peirceCut (e : R) (he : IsIdempotentElem e) : A →* A where
  toFun x := e • x + (1 - e) • (1 : A)
  map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
  map_mul' x y := by
    simp only [add_mul, mul_add, smul_mul_smul_comm, he.eq, he.mul_one_sub_self,
      he.one_sub_mul_self, he.one_sub.eq, zero_smul, add_zero, zero_add, mul_one]

variable {A}

end GlobalTheory.PeirceDecompositionCut
