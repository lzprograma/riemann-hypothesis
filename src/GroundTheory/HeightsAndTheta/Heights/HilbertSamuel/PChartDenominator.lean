module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartDenominator
import Mathlib.RingTheory.Localization.Finiteness

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem exists_nat_mul_mem_adjoin_int {Ω : Type} [Field Ω] [CharZero Ω] (S : Set Ω) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ S) : ∃ n : ℕ, 1 ≤ n ∧ (n : Ω) * x ∈ Algebra.adjoin ℤ S := by
  obtain ⟨t, ht⟩ := multiple_mem_adjoin_of_mem_localization_adjoin (nonZeroDivisors ℤ) ℚ S x hx
  refine ⟨t.1.natAbs, Int.natAbs_pos.mpr (nonZeroDivisors.ne_zero t.2), ?_⟩
  have ht' : (t.1 : Ω) * x ∈ Algebra.adjoin ℤ S := by simpa [Submonoid.smul_def, zsmul_eq_mul] using ht
  rcases Int.natAbs_eq t.1 with h | h
  · rwa [← Int.cast_natCast, ← h]
  · rw [← Int.cast_natCast, neg_eq_iff_eq_neg.mp h.symm, Int.cast_neg, neg_mul]
    exact neg_mem ht'

theorem ChartDenominator.proof : ChartDenominator.Statement := by
  intro K _ ι _ Ω _ _ y b τ s hs
  classical
  have key : ∀ c : ∀ k, ι k, ∃ n : ℕ, 1 ≤ n ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (n : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k))) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n, hn, h⟩ := exists_nat_mul_mem_adjoin_int _ (hs c hc)
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, le_rfl, fun h => absurd h hc⟩
  choose N hN1 hN using key
  refine ⟨∏ c, N c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun c _ => by
    have := hN1 c; omega), ?_⟩
  intro c hc
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ c)
  have h : ((∏ c, N c : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k)) =
      (m : ℤ) • ((N c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * b k)))) := by
    rw [hm]; simp only [Nat.cast_mul, zsmul_eq_mul, Int.cast_natCast]; ring
  rw [h]
  exact zsmul_mem (hN c hc) _

end GroundTheory.Heights₂.Heights.HilbertSamuel
