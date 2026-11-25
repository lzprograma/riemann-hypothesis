module

import Lemmata.NatMulIsIntegral.ExistsNatMulIsIntegral
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace Bl.general_b_fact_third_version

open NumberField in
theorem goal1 {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V]
    [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (Λ : Submodule (𝓞 E) V) (hΛ : Submodule.IsFullLattice E Λ) (v : V) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : E) • v ∈ Λ := by
  obtain ⟨m, hm, hv⟩ := Bl.NatMulIsIntegral.goal1 (L := Λ) (z := v) (by
    rw [hΛ.span_eq_top]
    exact Submodule.mem_top)
  exact ⟨m, hm.ne', by simpa only [Nat.cast_smul_eq_nsmul] using hv⟩

end Bl.general_b_fact_third_version
