module

public import Formalism.LogVandermondeBounds.LogVandermondeVariationUnbounded
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

namespace Formalism.LogVandermondeBounds.StandardLattice
open Finset

theorem eulerProductBounds : EulerProductBounds := by
  intro q hq n
  set x := q⁻¹
  have hx : 0 < x := inv_pos.mpr (by linarith)
  have hx3 : x ≤ 1 / 3 := by
    nlinarith [show x * q = 1 from inv_mul_cancel₀ (by linarith),
      mul_le_mul_of_nonneg_left (show 3 ≤ q by linarith) hx.le]
  have hx1 : x ≤ 1 := hx3.trans (by norm_num)
  refine ⟨?_, Finset.prod_le_one₀ (fun i _ => sub_nonneg.mpr (pow_le_one₀ hx.le hx1))
    (fun i _ => sub_le_self _ (pow_nonneg hx.le _))⟩
  suffices h : 1 - 2 * x + x ^ (n + 1) ≤ (1 - x) * ∏ i ∈ range n, (1 - x ^ (i + 1)) by
    by_contra! hlt
    linarith [mul_lt_mul_of_pos_left hlt (show 0 < 1 - x by linarith), pow_pos hx (n + 1)]
  induction n with
  | zero => simp; linarith
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, pow_succ x (n + 1)]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr (pow_le_one₀ hx.le hx1)))
    nlinarith only [mul_le_mul_of_nonneg_left
      (show x ^ (n + 1) ≤ x from pow_le_of_le_one hx.le hx1 (by omega)) (pow_nonneg hx.le (n + 1))]

end Formalism.LogVandermondeBounds.StandardLattice
