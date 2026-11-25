module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

namespace UpperTheory.V.Two.DyadicOrbitIndex

variable {Ω : Type} [Field Ω]

private theorem smul_val_lt [Algebra ℚ Ω] (g : G ℚ Ω) (A : ValuationSubring Ω) (n : ℕ)
    (hA : A.valuation (n : Ω) < 1) : (g • A).valuation (n : Ω) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or] at hA ⊢
  rcases hA with h | h
  · exact Or.inl h
  · refine Or.inr fun h' => h ?_
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at h'
    have e : g⁻¹ • ((n : Ω))⁻¹ = ((n : Ω))⁻¹ := by
      show (g⁻¹ : G ℚ Ω) ((n : Ω))⁻¹ = _
      rw [map_inv₀, map_natCast]
    rwa [e] at h'

end UpperTheory.V.Two.DyadicOrbitIndex

open UpperTheory.V.Two.DyadicOrbitIndex in
theorem UpperTheory.V.Two.orbIndex :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) (V : Subgroup (G ℚ Ω)) [V.Normal] (A₀ : ValuationSubring Ω), p.Prime → A₀.valuation (p : Ω) < 1 → (V ⊔ Dec (F := ℚ) A₀).index ≠ 0 → OrbLe V p (V ⊔ Dec (F := ℚ) A₀).index := by
  intro Ω _ _ _ p V hV A₀ hp h0 hi
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀)) := Nat.finite_of_card_ne_zero hi
  haveI := Fintype.ofFinite (G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀))
  refine ⟨Finset.univ.image fun q : G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀) => q.out • A₀, ?_, ?_, ?_⟩
  · refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
  · intro B hB
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hB
    exact smul_val_lt _ _ _ h0
  · intro A hA
    have hA0 := Formalism.BasicNotions.Examples₂.LB.isPlaceOver_vQ A₀ h0
    have hA1 := Formalism.BasicNotions.Examples₂.LB.isPlaceOver_vQ A hA
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) hA0 hA1
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (V ⊔ Dec (F := ℚ) A₀) g
    have hm : (h⁻¹ : G ℚ Ω) ∈ ((V ⊔ Dec (F := ℚ) A₀ : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := inv_mem h.2
    rw [Subgroup.normal_mul] at hm
    obtain ⟨v, hv, d, hd, e⟩ := hm
    set r := (QuotientGroup.mk g : G ℚ Ω ⧸ (V ⊔ Dec (F := ℚ) A₀)).out with hr
    refine ⟨r • A₀, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, r * v * r⁻¹, hV.conj_mem v hv r, ?_⟩
    have hd' : d • A₀ = A₀ := (mem_Dec (F := ℚ)).1 hd
    have eg : g = r * v * d := by
      have e' : v * d = (h : G ℚ Ω)⁻¹ := e
      rw [mul_assoc, e', hh]; group
    rw [eg, mul_smul (r * v) d, hd', smul_smul]
    congr 1; group
