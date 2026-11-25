module

public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Submodule

@[expose] public section

theorem UpperTheory.Reformulated.B.SmulMemOfSpanEqTop.exists_ne_zero_smul_mem_of_span_eq_top :
    ∀ {A : Type} [CommRing A] [IsDomain A]
    {K : Type} [Field K] [Algebra A K] [IsFractionRing A K] {V : Type} [AddCommGroup V]
    [_root_.Module K V] [_root_.Module A V] [IsScalarTower A K V] (M : Submodule A V),
    Submodule.span K (↑M : Set V) = ⊤ → ∀ (v : V), ∃ (d : A), d ≠ (0 : A) ∧ d • v ∈ M := by
  intro A _ _ K _ _ _ V _ _ _ _ M hM v
  have hv : v ∈ Submodule.span K (M : Set V) := hM ▸ Submodule.mem_top
  obtain ⟨w, hw, d, rfl⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors A)).mp hv
  refine ⟨d, nonZeroDivisors.ne_zero d.property, ?_⟩
  rw [← IsScalarTower.algebraMap_smul K, smul_smul, IsLocalization.mk'_spec',
    map_one, one_smul]
  simpa only [Submodule.span_eq] using hw
