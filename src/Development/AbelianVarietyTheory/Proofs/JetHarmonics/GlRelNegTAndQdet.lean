module

public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Finset

namespace GlobalTheory.CapelliNegT


open Finset in
theorem _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), _root_.Formalism.REAL.GlRel E →
      _root_.Formalism.REAL.GlRel (fun a b => -E b a) ∧
        ∀ u : ℂ, _root_.Formalism.REAL.qdet (fun a b => -E b a) u = ((-1 : ℂ) ^ n) • _root_.Formalism.REAL.qdet E ((n : ℂ) - 1 - u) := by
  intro A _ _ n E hE
  refine ⟨?_, fun u => ?_⟩
  · unfold _root_.Formalism.REAL.GlRel at hE ⊢
    intro a b c d
    have h := hE b a d c
    rw [neg_mul_neg, neg_mul_neg, h]
    simp only [@eq_comm _ a d, @eq_comm _ c b]
    split_ifs <;> abel
  · have hrow : ∀ v : ℂ, _root_.Formalism.REAL.qdet E v = _root_.PI.qminorRow E id id v := by
      intro v
      have key : _root_.PI.RowForm := _root_.quantum_minor_row_form
      unfold _root_.PI.RowForm at key
      exact key A n n E hE id id v
    have hM : ∀ (x : ℂ) (a b : Fin n),
        _root_.Formalism.REAL.Tm (fun a b => -E b a) x a b = -_root_.Formalism.REAL.Tm E (-x) b a := by
      intro x a b
      unfold _root_.Formalism.REAL.Tm
      by_cases h : a = b
      · subst h
        simp only [ite_true, map_neg]
        abel
      · simp only [h, Ne.symm h, ite_false]
        abel
    have hneg : ∀ g : Fin n → A, (List.ofFn fun k => -g k).prod = (-1) ^ n * (List.ofFn g).prod := by
      intro g
      have hl : (List.ofFn fun k => -g k) = (List.ofFn g).map Neg.neg := by
        rw [List.map_ofFn]
        rfl
      rw [hl, List.prod_map_neg, List.length_ofFn]
    have harg : ∀ k : Fin n, -(u - ((k : ℕ) : ℂ)) = (n : ℂ) - 1 - u - n + 1 + ((k : ℕ) : ℂ) := by
      intro k
      ring
    rw [hrow]
    unfold _root_.Formalism.REAL.qdet _root_.Formalism.REAL.qminor _root_.PI.qminorRow
    rw [Algebra.smul_def, map_pow, map_neg, map_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hM, hneg, harg, id]
    rw [← mul_assoc, ← mul_assoc, ((Commute.neg_one_right _).pow_right n).eq]

end GlobalTheory.CapelliNegT
