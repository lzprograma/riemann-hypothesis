module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

namespace Bl.general_b_fact_left

open Polynomial in
theorem goal1 {k : Type} [Field k] [Fintype k] (t m e : k) (hd : t ^ 2 - 4 * m ≠ 0) :
    ∃ x y : k, x ^ 2 + t * x * y + m * y ^ 2 = e := by
  by_cases hc : ringChar k = 2
  · obtain ⟨x, hx⟩ := FiniteField.isSquare_of_char_two hc e
    exact ⟨x, 0, by simpa [pow_two] using hx.symm⟩
  · obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (f := X ^ 2 - C e)
      (by rw [degree_sub_C, degree_X_pow] <;> norm_num)
      (degree_C_mul_X_pow 2 (sub_ne_zero.mpr (sub_ne_zero.mp hd).symm))
      (FiniteField.odd_card_of_char_ne_two hc)
    simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hab
    exact ⟨a - t * b, 2 * b, by linear_combination hab⟩

end Bl.general_b_fact_left
