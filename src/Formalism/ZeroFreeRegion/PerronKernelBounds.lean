module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Bounds for the Perron kernel away from its poles -/

@[expose] public section

open Complex

namespace Formalism.PerronKernel

private theorem norm_le_of_dist {z w : ℂ} {B P y d e : ℝ} (hy : 0 < y)
    (hd : 0 < d) (he : 0 < e) (hdw : d ≤ ‖w‖) (hew : e ≤ ‖w - 1‖)
    (hz : ‖z‖ ≤ B) (hp : y ^ w.re ≤ P) :
    ‖z * (y : ℂ) ^ w / (w * (w - 1))‖ ≤ B * P / (d * e) := by
  rw [norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hB := (norm_nonneg z).trans hz
  have hP := (Real.rpow_nonneg hy.le w.re).trans hp
  exact div_le_div₀ (mul_nonneg hB hP) (mul_le_mul hz hp (Real.rpow_nonneg hy.le _) hB)
    (mul_pos hd he) (mul_le_mul hdw hew he.le (norm_nonneg _))

/-- A lower bound on the height controls the distances to both real poles. -/
theorem norm_le {z w : ℂ} {B P y T : ℝ} (hy : 0 < y) (hT : 0 < T) (him : T ≤ |w.im|)
    (hz : ‖z‖ ≤ B) (hp : y ^ w.re ≤ P) :
    ‖z * (y : ℂ) ^ w / (w * (w - 1))‖ ≤ B * P / T ^ 2 := by
  rw [sq]
  exact norm_le_of_dist hy hT hT (him.trans (Complex.abs_im_le_norm _))
    (him.trans (by simpa using Complex.abs_im_le_norm (w - 1))) hz hp

/-- Between the poles a lower bound on the real part and a gap to one suffice;
the estimate also applies on the real axis itself. -/
theorem norm_left_le {z w : ℂ} {B P y ε : ℝ} (hy : 0 < y) (hε : 0 < ε)
    (hhalf : 1 / 2 ≤ w.re) (hgap : ε ≤ 1 - w.re) (hz : ‖z‖ ≤ B) (hp : y ^ w.re ≤ P) :
    ‖z * (y : ℂ) ^ w / (w * (w - 1))‖ ≤ B * P * (2 / ε) := by
  have hw : 1 / 2 ≤ ‖w‖ := hhalf.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have h := Complex.abs_re_le_norm (w - 1)
  rw [sub_re, one_re, abs_sub_comm] at h
  have hw' := hgap.trans ((le_abs_self _).trans h)
  exact (norm_le_of_dist hy (by norm_num : (0 : ℝ) < 1 / 2) hε hw hw' hz hp).trans_eq
    (by field_simp)

/-- On the standard right edge, the power factor is exactly exp(1) times y. -/
theorem norm_right_le (f : ℂ → ℂ) {C y t : ℝ} (hy : 1 < y) (ht : 0 < |t|)
    (hf : ∀ s : ℂ, 1 < s.re → ‖f s‖ ≤ 1 / (s.re - 1) + C) :
    let w : ℂ := ((1 + 1 / Real.log y : ℝ) : ℂ) + t * I
    ‖f w * (y : ℂ) ^ w / (w * (w - 1))‖ ≤ (Real.log y + C) * (Real.exp 1 * y) / t ^ 2 := by
  dsimp only
  set w : ℂ := ((1 + 1 / Real.log y : ℝ) : ℂ) + t * I
  have hl := Real.log_pos hy
  have hre : w.re = 1 + 1 / Real.log y := by simp [w]
  have hF : ‖f w‖ ≤ Real.log y + C := by
    simpa [hre, one_div] using hf w (by rw [hre]; linarith [one_div_pos.mpr hl])
  rw [← sq_abs t]
  apply norm_le (zero_lt_one.trans hy) ht (by simp [w]) hF
  rw [hre, Real.rpow_add (zero_lt_one.trans hy), Real.rpow_one,
    Real.rpow_def_of_pos (zero_lt_one.trans hy), mul_one_div_cancel hl.ne', mul_comm y]

end Formalism.PerronKernel
