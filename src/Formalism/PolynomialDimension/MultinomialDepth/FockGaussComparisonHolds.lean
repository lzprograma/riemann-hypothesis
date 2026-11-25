module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.TypeStar
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

theorem fock_mult_fact_le {α : Type*} (p : ℕ) (f : α → ℕ) (s : Finset α) :
    (Nat.multinomial s f).factorization p ≤ s.card * Nat.log p (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Nat.multinomial_insert ha, Nat.factorization_mul (Nat.choose_pos (Nat.le_add_right _ _)).ne'
    (Nat.multinomial_pos _ _).ne', Finsupp.add_apply, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
  have h1 := Nat.factorization_choose_le_log (p := p) (n := f a + ∑ i ∈ s, f i) (k := f a)
  have h2 : Nat.log p (∑ i ∈ s, f i) ≤ Nat.log p (f a + ∑ i ∈ s, f i) :=
    Nat.log_mono_right (Nat.le_add_left _ _)
  have h3 := Nat.mul_le_mul_left s.card h2
  rw [add_one_mul]
  omega

theorem fock_mult_val_le {α : Type*} (p : ℕ) [hp : Fact p.Prime] (f : α → ℕ) (s : Finset α) :
    padicValNat p (Nat.multinomial s f) ≤ s.card * Nat.log p (∑ i ∈ s, f i) := by
  rw [Nat.padicValNat_def, ← Nat.factorization_def _ hp.out]
  exact fock_mult_fact_le p f s

theorem fock_val_prod {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  simp only [Nat.padicValNat_def, ← Nat.factorization_def _ Fact.out,
    Nat.factorization_prod hf, Finsupp.finsetSum_apply]

end Formalism.CountingSumsFrames
