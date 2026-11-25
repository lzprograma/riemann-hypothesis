module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

open Polynomial Finset

namespace PadicInt

/-- Successively minimizing a polynomial on a compact set of units gives global
centres, with repetition allowed, without passing to a splitting field. -/
theorem exists_centres_polynomial {l : ℕ} [Fact l.Prime]
    (C : Set ℤ_[l]) (hC : IsCompact C) (hne : C.Nonempty)
    (hunit : ∀ y ∈ C, ‖y‖ = 1) (R : ℕ) (P : ℤ_[l][X])
    (hdeg : P.natDegree ≤ R) (hzero : ‖P.eval 0‖ = 1) :
    ∃ y : Fin R → ℤ_[l], (∀ i, y i ∈ C) ∧
      ∀ t ∈ C, (∏ i, ‖t - y i‖) ≤ ‖P.eval t‖ := by
  classical
  induction R generalizing P with
  | zero =>
    refine ⟨Fin.elim0, by simp, ?_⟩
    intro t ht
    have hp := eq_C_of_natDegree_le_zero hdeg
    rw [hp] at hzero ⊢
    simpa only [eval_C, Fin.prod_univ_zero] using hzero.ge
  | succ R ih =>
    obtain ⟨y, hy, hmin⟩ := hC.exists_isMinOn hne P.continuous.norm.continuousOn
    by_cases hone : ‖P.eval y‖ = 1
    · refine ⟨fun _ => y, fun _ => hy, fun t ht => ?_⟩
      exact (prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => norm_le_one _)).trans
        (hone ▸ hmin ht)
    have hlt : ‖P.eval y‖ < 1 := lt_of_le_of_ne (norm_le_one _) hone
    let Q := P /ₘ (X - Polynomial.C y)
    have heval (t : ℤ_[l]) : P.eval t = P.eval y + (t - y) * Q.eval t := by
      conv_lhs => rw [← modByMonic_add_div P (X - Polynomial.C y)]
      rw [modByMonic_X_sub_C_eq_C_eval]
      simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X, Q]
    have hQ : ‖Q.eval 0‖ = 1 := by
      apply le_antisymm (norm_le_one _)
      by_contra h
      have hh := IsUltrametricDist.norm_add_le_max (P.eval y) ((0 - y) * Q.eval 0)
      rw [← heval, hzero, zero_sub, norm_mul, norm_neg, hunit y hy, one_mul] at hh
      exact (not_lt_of_ge hh) (max_lt hlt (lt_of_not_ge h))
    have hQdeg : Q.natDegree ≤ R := by
      dsimp only [Q]
      rw [natDegree_divByMonic P (monic_X_sub_C y), natDegree_X_sub_C]
      lia
    obtain ⟨ys, hys, hb⟩ := ih Q hQdeg hQ
    refine ⟨Fin.cons y ys, ?_, fun t ht => ?_⟩
    · intro i
      refine Fin.cases hy (fun k => hys k) i
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      calc
        _ ≤ ‖t - y‖ * ‖Q.eval t‖ := mul_le_mul_of_nonneg_left (hb t ht) (norm_nonneg _)
        _ = ‖P.eval t - P.eval y‖ := by rw [heval, add_sub_cancel_left, norm_mul]
        _ ≤ ‖P.eval t‖ := by
          calc
            _ ≤ max ‖P.eval t‖ ‖P.eval y‖ := by
              simpa only [sub_eq_add_neg, norm_neg] using
                IsUltrametricDist.norm_add_le_max (P.eval t) (-P.eval y)
            _ = _ := max_eq_left (hmin ht)

end PadicInt
