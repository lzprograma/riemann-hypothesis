module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ToDual
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Order.Basic
import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

open scoped PowerSeries Pointwise

namespace GlobalTheory

theorem numerical_bounds_of_forty_mul_lt : ∀ (l H N η r : ℕ), 2 ≤ N → 1 ≤ η → η < H → 4 * r ≤ N ^ 2 →
    40 * (H * N ^ 2 + N ^ 3) < l →
    2 * (H + η + 2 * (N - 1) * r + 1) + 2 < l ∧ 10 * H + 2 ≤ l ∧ 14 * H + (N + 2) * η < l ∧
      8 * H + 1 < l ∧ 4 * η * r + 4 < l ∧ (r + 2) * η < l + 1 := by
  intro l H N η r hN hη hηH hr hl
  have hN2 : 4 ≤ N ^ 2 := by
    simpa using Nat.pow_le_pow_left hN 2
  have hH : 2 ≤ H := by omega
  have hHN : 4 * H ≤ H * N ^ 2 := by
    calc 4 * H = H * 4 := by ring
      _ ≤ H * N ^ 2 := Nat.mul_le_mul_left H hN2
  have hN3 : 8 ≤ N ^ 3 := by
    simpa using Nat.pow_le_pow_left hN 3
  have hNr : 4 * (N * r) ≤ N ^ 3 := by
    calc 4 * (N * r) = N * (4 * r) := by ring
      _ ≤ N * N ^ 2 := Nat.mul_le_mul_left N hr
      _ = N ^ 3 := by ring
  have hsub : (N - 1) * r ≤ N * r := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hηr : 4 * (η * r) ≤ H * N ^ 2 := by
    calc 4 * (η * r) ≤ 4 * (H * r) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right r hηH.le)
      _ = H * (4 * r) := by ring
      _ ≤ H * N ^ 2 := Nat.mul_le_mul_left H hr
  have hN2' : N + 2 ≤ N ^ 2 := by
    calc N + 2 ≤ 2 * N := by omega
      _ = N * 2 := by ring
      _ ≤ N * N := Nat.mul_le_mul_left N hN
      _ = N ^ 2 := by ring
  have hNη : (N + 2) * η ≤ H * N ^ 2 := by
    calc (N + 2) * η ≤ (N + 2) * H := Nat.mul_le_mul_left _ hηH.le
      _ ≤ N ^ 2 * H := Nat.mul_le_mul_right H hN2'
      _ = H * N ^ 2 := by ring
  have hr4 : r ≤ 4 * r := by omega
  have hrN : r ≤ N ^ 2 := le_trans hr4 hr
  have hrη : r * η ≤ H * N ^ 2 := by
    calc r * η ≤ r * H := Nat.mul_le_mul_left r hηH.le
      _ ≤ N ^ 2 * H := Nat.mul_le_mul_right H hrN
      _ = H * N ^ 2 := by ring
  have h2η : 2 * η ≤ H * N ^ 2 := by omega
  have hsum1 : 1 ≤ H * N ^ 2 + N ^ 3 := by
    have := Nat.mul_le_mul hH hN2
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 2 * (N - 1) * r = 2 * ((N - 1) * r) by ring]
    omega
  · omega
  · omega
  · omega
  · rw [show 4 * η * r = 4 * (η * r) by ring]
    omega
  · rw [show (r + 2) * η = r * η + 2 * η by ring]
    omega

end GlobalTheory
