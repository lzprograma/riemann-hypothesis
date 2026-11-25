module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsFurther
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCurveSmallCountLower
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionPointHeight
import Mathlib.Algebra.Order.Star.Real

@[expose] public section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter
noncomputable section

namespace ArithmeticVolumeBigDimensionOne
theorem le_limsup_div {u : ℕ → ℝ} {T C C' : ℝ}
    (hlo : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * T - C ≤ u n) (hup : ∀ n : ℕ, u n ≤ C' * ((n : ℝ) + 1)) :
    T ≤ limsup (fun n : ℕ => u n / n) atTop := by
  refine le_of_forall_pos_le_add fun ε hε => sub_le_iff_le_add.mp ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
  refine le_limsup_of_frequently_le (Eventually.frequently ?_) ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ), eventually_ge_atTop N] with n hn hnN
    rw [le_div_iff₀ (by exact_mod_cast hn)]
    nlinarith only [hlo n hn, (div_lt_iff₀ hε).mp
      (hN.trans_le (show (N : ℝ) ≤ n by exact_mod_cast hnN))]
  · refine isBoundedUnder_of_eventually_le (a := 2 * |C'|) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [div_le_iff₀ (by exact_mod_cast (show 0 < n from hn))]
    calc u n ≤ |C'| * ((n : ℝ) + n) := (hup n).trans
          (mul_le_mul (le_abs_self _) (add_le_add le_rfl (by exact_mod_cast hn)) (by positivity) (abs_nonneg _))
         _ = 2 * |C'| * n := by ring
end ArithmeticVolumeBigDimensionOne

theorem ArithmeticVolumeBigDimensionOne.proof (hP : PackingStatement) (hL : CurveSmallCountLower.Statement) :
    ArithmeticVolumeBigDimensionOne.Statement := by
  intro K _ ι _ Ω _ y A P0 II hII har hb hP0 hs hnef hc
  obtain ⟨C, hC⟩ := hL K ι Ω y A II hII har hb hs.1 hc
  obtain ⟨-, C', hC'⟩ := hP K ι Ω y 0 A (chartLat y A.a) har hb hs.1
    (fun τ => SmallSectionPointHeight.chartLat_le_chartLatNm y A.a τ)
  simpa [arVolP] using
    ArithmeticVolumeBigDimensionOne.le_limsup_div hC (fun n => by simpa using hC' n)

end
end GroundTheory.Heights₂.Heights.HilbertSamuel
