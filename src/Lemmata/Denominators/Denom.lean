module

import Lemmata.NatMulIsIntegral.ExistsNatMulIsIntegral
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open NumberField

namespace Bl.DenominatorsAlt

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem goal1 (M : Submodule (𝓞 E) (Fin n → E)) (hsp : Submodule.span E (M : Set (Fin n → E)) = ⊤)
    (v : Fin n → E) : ∃ m : ℕ, 0 < m ∧ (m : 𝓞 E) • v ∈ M := by
  obtain ⟨m, hm, hmem⟩ := Bl.NatMulIsIntegral.goal1 (L := M) (z := v)
    (by rw [hsp]; exact Submodule.mem_top)
  exact ⟨m, hm, by simpa only [Nat.cast_smul_eq_nsmul] using hmem⟩

end Bl.DenominatorsAlt
