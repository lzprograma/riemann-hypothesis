module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.Integral

@[expose] public section

namespace GlobalTheory

theorem unitBall_eq_of_integral_dvr (p : ℕ) [Fact p.Prime] (V W : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V W]
    [Algebra.IsIntegral V W] [IsLocalHom (algebraMap V W)]
    (hinj : Function.Injective (algebraMap V W))
    (κ : FractionRing V →+* PadicAlgCl p) (κ' : FractionRing W →+* PadicAlgCl p)
    (hc : ∀ v : V, κ' (algebraMap W (FractionRing W) (algebraMap V W v)) =
      κ (algebraMap V (FractionRing V) v))
    (hV : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) :
    ∀ x, ‖κ' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap W (FractionRing W)) := by
  let φ : W →+* PadicAlgCl p := κ'.comp (algebraMap W (FractionRing W))
  let vP : Valuation (PadicAlgCl p) NNReal := Valued.v
  let ψ : V →+* vP.integer :=
    (κ.comp (algebraMap V (FractionRing V))).codRestrict vP.integer fun a =>
      (Valuation.mem_integer_iff vP _).2
        (show ‖κ (algebraMap V (FractionRing V) a)‖₊ ≤ 1 from
          NNReal.coe_le_coe.1 (by simpa using (hV _).2 ⟨a, rfl⟩))
  have hW1 : ∀ w : W, ‖φ w‖ ≤ 1 := fun w => by
    obtain ⟨q, hqm, hq⟩ := Algebra.IsIntegral.isIntegral (R := V) w
    have hint : IsIntegral vP.integer (φ w) := ⟨q.map ψ, hqm.map ψ, by
      rw [Polynomial.eval₂_map, show (algebraMap vP.integer (PadicAlgCl p)).comp ψ =
        φ.comp (algebraMap V W) from RingHom.ext fun a => (hc a).symm]
      exact (Polynomial.hom_eval₂ q (algebraMap V W) φ w).symm.trans (by rw [hq, map_zero])⟩
    exact NNReal.coe_le_coe.1 ((Valuation.mem_integer_iff vP _).1
      ((Valuation.integer.integers vP).mem_of_integral hint))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hπ1 : ‖κ (algebraMap V (FractionRing V) π)‖ < 1 := by
    refine lt_of_le_of_ne ((hV _).2 ⟨π, rfl⟩) fun h => hπ.not_isUnit ?_
    obtain ⟨a, ha⟩ := (hV _).1 (by rw [map_inv₀, norm_inv, h, inv_one])
    refine isUnit_iff_exists_inv.2 ⟨a, IsFractionRing.injective V (FractionRing V) ?_⟩
    have hπ0 := (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hπ.ne_zero
    rw [map_mul, ha, mul_inv_cancel₀ hπ0, map_one]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hϖ1 : ‖φ ϖ‖ < 1 := by
    obtain ⟨e, u, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      ((map_ne_zero_iff _ hinj).2 hπ.ne_zero) hϖ
    have hnorm : ‖φ ϖ‖ ^ e < 1 := by
      have hpow : ϖ ^ e = ↑u⁻¹ * algebraMap V W π := by
        rw [he, ← mul_assoc, Units.inv_mul, one_mul]
      calc ‖φ ϖ‖ ^ e = ‖φ (ϖ ^ e)‖ := by rw [map_pow, norm_pow]
        _ = ‖φ ↑u⁻¹‖ * ‖κ (algebraMap V (FractionRing V) π)‖ := by
          rw [hpow, map_mul, norm_mul, show φ (algebraMap V W π) = _ from hc π]
        _ ≤ 1 * ‖κ (algebraMap V (FractionRing V) π)‖ :=
          mul_le_mul_of_nonneg_right (hW1 ↑u⁻¹) (norm_nonneg _)
        _ < 1 := by rwa [one_mul]
    by_contra h
    exact (one_le_pow₀ (not_lt.1 h)).not_gt hnorm
  intro x
  refine ⟨fun hx => ?_, fun ⟨w, hw⟩ => hw ▸ hW1 w⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, map_zero _⟩
  rcases ValuationRing.isInteger_or_isInteger W x with h | ⟨a, ha⟩
  · exact h
  by_cases hu : IsUnit a
  · obtain ⟨u, rfl⟩ := hu
    exact ⟨↑u⁻¹, by rw [map_units_inv, ha, inv_inv]⟩
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 <|
    hϖ.maximalIdeal_eq ▸ (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hu)
  suffices (1 : ℝ) < 1 from this.false.elim
  calc (1 : ℝ) ≤ ‖κ' x‖⁻¹ :=
        (one_le_inv₀ (norm_pos_iff.2 ((map_ne_zero_iff κ' κ'.injective).2 hx0))).2 hx
    _ = ‖κ' x⁻¹‖ := by rw [map_inv₀, norm_inv]
    _ = ‖φ ϖ‖ * ‖φ b‖ := by
        rw [← ha, show κ' (algebraMap W (FractionRing W) (ϖ * b)) = φ (ϖ * b) from rfl,
          map_mul, norm_mul]
    _ ≤ ‖φ ϖ‖ * 1 := mul_le_mul_of_nonneg_left (hW1 b) (norm_nonneg _)
    _ < 1 := by rwa [mul_one]

end GlobalTheory
