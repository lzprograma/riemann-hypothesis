module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.Finiteness

@[expose] public section

namespace GlobalTheory.SmulMemSpanIntegers

theorem exists_smul_mem_span_integers {Ks : Type} [Field Ks] [NumberField Ks] {WL : Type}
    [AddCommGroup WL] [Module Ks WL] [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {T : Set WL} {g : WL}
    (hg : g ∈ Submodule.span Ks T) :
    ∃ d : NumberField.RingOfIntegers Ks, d ≠ 0 ∧
      d • g ∈ Submodule.span (NumberField.RingOfIntegers Ks) T := by
  obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers Ks)) Ks T g hg
  exact ⟨d, nonZeroDivisors.coe_ne_zero d, hd⟩

end GlobalTheory.SmulMemSpanIntegers
