module

import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneFixRoots
import Mathlib.Tactic.Linter.Style
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Formalism.GaloisCohomology.Statement

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank
open Formalism.BasicNotions.Examples₂.LB (vQ isPlaceOver_vQ)

namespace UpperTheory.V.LDataCardLeFinrank.DecompositionFrobenius

variable (l : ℕ) [hl : Fact l.Prime]

private theorem normV_vQ : normV (vQ l) = l := by
  show Nat.card (𝓞 ℚ ⧸ Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l
  have hJ : Ideal.span {((l : ℕ) : ℤ)} = Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [Nat.card_congr ((Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv hJ).trans (Int.quotientSpanNatEquivZMod l)).toEquiv, Nat.card_zmod]

variable {l} {Ω : Type} [Field Ω]

private theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  apply _root_.Formalism.BasicNotions.Examples₂.LB.val_intCast_lt_one_iff <;> assumption

end UpperTheory.V.LDataCardLeFinrank.DecompositionFrobenius

open UpperTheory.V.LDataCardLeFinrank.DecompositionFrobenius in
theorem UpperTheory.V.LDataCardLeFinrank.decFrob :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∃ g ∈ Dec (F := ℚ) A, ∀ m : ℕ, m.Coprime l → ∀ ζ : Ω, ζ ^ m = 1 → g ζ = ζ ^ l := by
  intro Ω _ _ _ l _ A hA
  have hP : IsPlaceOver (F := ℚ) A (vQ l) := isPlaceOver_vQ A (by exact_mod_cast hA)
  obtain ⟨σ, hσD, hσ⟩ := exists_isFrob hP
  rw [normV_vQ] at hσ
  refine ⟨σ, hσD, fun m hm ζ hζ => ?_⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : l.Prime).one_lt.ne' (by simpa using hm)
  have hζv : A.valuation ζ ≤ 1 := by
    by_contra h
    have h2 := one_lt_pow' (not_le.mp h) hm0
    rw [← map_pow, hζ, map_one] at h2
    exact lt_irrefl _ h2
  have key := (ineFixRoots ℚ Ω l A hA m hm (ζ ^ l) (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow])).1
  apply key (σ ζ)
  · rw [← map_pow, hζ, map_one]
  · exact hσ ζ hζv
