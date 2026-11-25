module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.FractionRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

namespace GlobalTheory.CompanionTheory.QuadFin

theorem exists_eq_add_mul_of_mem_adjoin {E : Type*} [Field E] [Algebra ℚ E] (x : E) (c : ℚ)
    (hx : x ^ 2 = algebraMap ℚ E c) {y : E} (hy : y ∈ IntermediateField.adjoin ℚ {x}) :
    ∃ a b : ℚ, y = algebraMap ℚ E a + algebraMap ℚ E b * x := by
  have hint : IsIntegral ℚ x :=
    ⟨Polynomial.X ^ 2 - Polynomial.C c, Polynomial.monic_X_pow_sub_C c two_ne_zero, by simp [hx]⟩
  have hy' : y ∈ Algebra.adjoin ℚ {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  refine Algebra.adjoin_induction (fun z hz => ?_) (fun r => ?_) (fun u v _ _ hu hv => ?_)
    (fun u v _ _ hu hv => ?_) hy'
  · exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hz]; simp⟩
  · exact ⟨r, 0, by simp⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    exact ⟨a + a', b + b', by simp only [map_add (f := _)]; ring⟩
  · obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨a', b', rfl⟩ := hv
    refine ⟨a * a' + b * b' * c, a * b' + a' * b, ?_⟩
    simp only [map_add (f := _), map_mul]
    linear_combination (algebraMap ℚ E b * algebraMap ℚ E b') * hx

end GlobalTheory.CompanionTheory.QuadFin
