module

public import Formalism.PadicSubsetSums.CentralIdempotents.StretchedExponentialDominance
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem dominant_numbers_sharp_holds : StretchedExponentialDominance := by
  intro C ε hε
  have ha : 0 < ε / 6 := by positivity
  filter_upwards [(tendsto_rpow_atTop (show 0 < ε / 6 - ε / 7 by linarith)).eventually_ge_atTop 3,
    (isLittleO_log_rpow_atTop ha).bound (show (0 : ℝ) < 1 / (3 * (|C| + 1)) by positivity),
    (tendsto_rpow_atTop ha).eventually_ge_atTop (3 * Real.log 20),
    Filter.eventually_ge_atTop (1 : ℝ)] with x hgap hlog h20 hx
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _),
    one_div, mul_comm (3 * (|C| + 1))⁻¹, ← div_eq_mul_inv, le_div_iff₀ (by positivity)] at hlog
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_add,
    show (1 : ℝ) / 20 = Real.exp (-Real.log 20) by
      rw [Real.exp_neg, Real.exp_log (by norm_num), one_div],
    ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [abs_nonneg (Real.log x), le_abs_self (C * Real.log x), abs_mul C (Real.log x),
    show 3 * x ^ (ε / 7) ≤ x ^ (ε / 6) by
      simpa only [← Real.rpow_add hx0, sub_add_cancel] using
        mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hx0.le (ε / 7))]

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
