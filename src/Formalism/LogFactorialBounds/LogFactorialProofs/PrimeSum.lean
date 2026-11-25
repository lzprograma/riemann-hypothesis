module

import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.FirstTermSizeBound
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.NumberTheory.Primorial

@[expose] public section

noncomputable section

namespace Formalism.LogFactorialBounds

open Finset Real

lemma div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n / p ≤ (n.factorial).factorization p := by
  rcases Nat.lt_or_ge n p with h | h
  · rw [Nat.div_eq_of_lt h]
    exact Nat.zero_le _
  · rw [Nat.factorization_factorial hp (Nat.lt_succ_self (Nat.log p n))]
    have hpos : 0 < Nat.log p n := Nat.log_pos hp.one_lt h
    have h1 : 1 ∈ Finset.Ico 1 (Nat.succ (Nat.log p n)) :=
      Finset.mem_Ico.2 ⟨le_rfl, by omega⟩
    have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simpa using this

lemma sum_div_mul_log_le_log_factorial (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, ((n / p : ℕ) : ℝ) * Real.log p ≤ Real.log (n.factorial : ℕ) := by
  apply Formalism.MainNotions.WeilJacquetShalikaLaw.Proof.sz_sum_div_log

lemma log_factorial_le (n : ℕ) : Real.log (n.factorial : ℕ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : (0 : ℝ) < (n.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos n
    have h2 : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    calc Real.log (n.factorial : ℕ) ≤ Real.log ((n : ℝ) ^ n) := Real.log_le_log h1 h2
      _ = n * Real.log n := by rw [Real.log_pow]

lemma sum_primesLE_log_div_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  apply Formalism.MainNotions.WeilJacquetShalikaLaw.Proof.sz_mertens <;> assumption

end Formalism.LogFactorialBounds
