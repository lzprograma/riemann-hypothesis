module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.RingTheory.Localization.Finiteness

@[expose] public section

universe u_1 u_2

namespace Bl.ClearingDenominators

private lemma umon_le_uzmon {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (E : Formalism.MainNotions.G.GLOps n K V) : Formalism.MainNotions.G.Umon E ≤ Formalism.MainNotions.G.UZmon E := by
  unfold Formalism.MainNotions.G.Umon
  rw [Submonoid.closure_le]
  rintro _ ⟨⟨a, b⟩, rfl⟩
  refine Submonoid.subset_closure ?_
  simp only [Formalism.MainNotions.G.UZgens, Set.mem_ofPred_eq]
  by_cases h : a = b
  · subst h
    exact Or.inr ⟨a, 1, by simp [Formalism.MainNotions.G.binomE]⟩
  · exact Or.inl ⟨a, b, 1, h, by simp [Formalism.MainNotions.G.divPowE]⟩

private lemma clear_den {O K V : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (D : Submodule O V) (S : Set V) (hS : S ⊆ D) (y : V) (hy : y ∈ Submodule.span K S) :
    ∃ o : O, o ≠ 0 ∧ o • y ∈ D := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) K S y hy
  exact ⟨t, nonZeroDivisors.ne_zero t.2, (Submodule.span_le.mpr hS) ht⟩

open Formalism.MainNotions.G in
theorem goal1
    {n : ℕ} {O : Type u_1} [inst : CommRing O] [inst_1 : IsDomain O] [IsDiscreteValuationRing O]
    {V : Type u_2} [inst_3 : AddCommGroup V] [inst_4 : Module (KK O) V] [inst_5 : Module O V]
    [inst_6 : IsScalarTower O (KK O) V]
    {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} :
    IsIrrHW E lam v → ∀ y : V, ∃ o : O, o ≠ 0 ∧ o • y ∈ Delta (O := O) E v := by
  intro h y
  have hy : y ∈ Submodule.span (KK O) {x | ∃ u ∈ Umon E, x = u v} := by
    rw [h.2.2.2]
    exact Submodule.mem_top
  refine clear_den _ {x | ∃ u ∈ Umon E, x = u v} ?_ y hy
  rintro x ⟨u, hu, rfl⟩
  simp only [Formalism.MainNotions.G.Delta, SetLike.mem_coe]
  exact Submodule.subset_span ⟨u, umon_le_uzmon E hu, rfl⟩

end Bl.ClearingDenominators
