module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelAdjoinRootsIntegrallyClosedQuotient
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

namespace GlobalTheory.K5.IntFrac

open Polynomial

theorem mem_of_div_le_one : ∀ (O Ω : Type) [CommRing O] [Field Ω] [Algebra O Ω] (v : Valuation Ω NNReal), (∀ x : Ω, v x ≤ 1 ↔ IsIntegral O x) →
  ∀ (B : Subalgebra O Ω), (∀ x ∈ B, v x ≤ 1) → ∀ π ∈ B, π ≠ 0 → v π < 1 → (∀ x ∈ B, v x < 1 → x / π ∈ B) →
  ∀ a ∈ B, ∀ b ∈ B, v (a / b) ≤ 1 → a / b ∈ B := by
  intro O Ω _ _ _ v hv B hB π hπB hπ0 hπ1 hdiv
  have hvπ : 0 < v π := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hπ0)
  have hA : ∀ n : ℕ, ∀ a ∈ B, v (a / π ^ n) ≤ 1 → a / π ^ n ∈ B := by
    intro n
    induction n with
    | zero => intro a ha _; simpa using ha
    | succ k ih =>
      intro a ha hle
      have hlt : v a < 1 := by
        have he : v a = v (a / π ^ (k + 1)) * v π ^ (k + 1) := by
          rw [map_div₀, map_pow, div_mul_cancel₀]
          exact pow_ne_zero _ hvπ.ne'
        rw [he]
        calc v (a / π ^ (k + 1)) * v π ^ (k + 1) ≤ 1 * v π ^ (k + 1) := by gcongr
          _ < 1 := by
            rw [one_mul]
            exact pow_lt_one₀ hvπ.le hπ1 (Nat.succ_ne_zero k)
      have he : a / π ^ (k + 1) = a / π / π ^ k := by rw [pow_succ', div_div]
      rw [he] at hle ⊢
      exact ih _ (hdiv a ha hlt) hle
  intro a ha b hb hab
  by_cases hb0 : b = 0
  · rw [hb0, div_zero]
    exact B.zero_mem
  have hvb : 0 < v b := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hb0)
  have hex : ∃ n, v π ^ (n + 1) < v b := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hvb hπ1
    cases m with
    | zero => exact absurd (hB b hb) (not_le.mpr (by simpa using hm))
    | succ k => exact ⟨k, hm⟩
  classical
  set n := Nat.find hex with hndef
  have hn : v π ^ (n + 1) < v b := Nat.find_spec hex
  have hle : v b ≤ v π ^ n := by
    by_cases h0 : n = 0
    · rw [h0, pow_zero]
      exact hB b hb
    · have hmin := Nat.find_min hex (show n - 1 < n by omega)
      have hn1 : n - 1 + 1 = n := by omega
      rw [hn1] at hmin
      exact not_lt.mp hmin
  have hvπn : 0 < v π ^ n := pow_pos hvπ n
  have hvw_le : v (b / π ^ n) ≤ 1 := by
    rw [map_div₀, map_pow, div_le_one₀ hvπn]
    exact hle
  have hwB : b / π ^ n ∈ B := hA n b hb hvw_le
  have hvw : v (b / π ^ n) = 1 := by
    refine le_antisymm hvw_le (not_lt.mp fun hlt => ?_)
    have h2 := hB _ (hdiv _ hwB hlt)
    rw [div_div, ← pow_succ, map_div₀, map_pow, div_le_one₀ (pow_pos hvπ _)] at h2
    exact not_le.mpr hn h2
  have hw0 : b / π ^ n ≠ 0 := by
    intro h
    rw [h, map_zero] at hvw
    exact zero_ne_one hvw
  have hwinv : (b / π ^ n)⁻¹ ∈ B := by
    have hint : IsIntegral O (b / π ^ n)⁻¹ := (hv _).mp (by rw [map_inv₀, hvw, inv_one])
    have hmem := GlobalTheory.K5.LevClosed.mem_adjoin_inv_of_isIntegral (inv_ne_zero hw0) hint
    rw [inv_inv] at hmem
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hwB) hmem
  have haπ : a / π ^ n ∈ B := by
    apply hA n a ha
    have he : a / π ^ n = a / b * (b / π ^ n) := by field_simp
    rw [he, map_mul, hvw, mul_one]
    exact hab
  have he : a / b = a / π ^ n * (b / π ^ n)⁻¹ := by field_simp
  rw [he]
  exact B.mul_mem haπ hwinv

end GlobalTheory.K5.IntFrac
