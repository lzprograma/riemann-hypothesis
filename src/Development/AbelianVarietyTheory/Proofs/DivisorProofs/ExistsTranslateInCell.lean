module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul

@[expose] public section

open Matrix

namespace GlobalTheory.KSp

variable {k : Type} [Field k] {ν : Type} [Fintype ν] [DecidableEq ν]

theorem transv_kills (c : k →+* k) (S A C : Matrix ν ν k)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : ν → k) (hu : A *ᵥ u = 0) (w : ν → k) :
    ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w)) = 0 := by
  have h := congrArg (fun M => u ⬝ᵥ (M *ᵥ (c ∘ w))) hiso
  simp only [add_mulVec, dotProduct_add, dotProduct_mulVec, zero_mulVec, dotProduct_zero] at h
  have e1 : u ᵥ* (Aᵀ * S * C.map c) = 0 := by
    rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, hu, zero_vecMul, zero_vecMul]
  have e2 : u ᵥ* (Cᵀ * S * A.map c) ⬝ᵥ (c ∘ w) = ((C *ᵥ u) ᵥ* S) ⬝ᵥ (c ∘ (A *ᵥ w)) := by
    rw [← vecMul_vecMul, ← dotProduct_mulVec, ← vecMul_vecMul, vecMul_transpose]
    congr 1
    funext i
    exact (RingHom.map_mulVec c A w i).symm
  rw [e1, zero_dotProduct, zero_add, e2] at h
  exact h

end GlobalTheory.KSp
