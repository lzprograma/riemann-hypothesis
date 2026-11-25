module

import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatSmulMem
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace GlobalTheory.NatMulIntegral

open NumberField

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  apply GlobalTheory.PrincLat.exists_nat_smul_mem <;> assumption

end GlobalTheory.NatMulIntegral
