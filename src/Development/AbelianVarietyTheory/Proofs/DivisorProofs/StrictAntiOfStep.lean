module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

open GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem strictAnti_of_step {N : ℕ} {α : Type} [Preorder α] (f : Fin N → α)
    (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b < f a) : StrictAnti f := by
  cases N with
  | zero => intro a; exact a.elim0
  | succ n =>
    rw [Fin.strictAnti_iff_succ_lt]
    intro i
    exact h _ _ (by simp)

theorem divided_strictAnti : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ,
    StrictAnti (W.u1 τ) ∧ StrictAnti (W.u' τ) ∧ StrictAnti (fun i => (W.u1 τ i : ℝ)) := by
  intro ι _ N W H hD τ
  have hT : (4 : ℤ) ≤ W.T := by have := H.h1; omega
  have hh : (0 : ℤ) < W.h0 := by
    obtain ⟨k1, _⟩ := H.h2
    have := H.weightConst_nonneg
    omega
  have step : ∀ a b : Fin N, (b : ℕ) = a + 1 → W.u1 τ b < W.u1 τ a ∧ W.u' τ b < W.u' τ a := by
    intro a b hab
    obtain ⟨g1, g2, _⟩ := divided_gaps ι N W H hD τ a b hab
    by_cases hb : (b : ℕ) = W.p
    · obtain ⟨e1, e2⟩ := g2 hb
      have ha : ¬ ((b : ℕ) < W.p) := by omega
      have ha' : (a : ℕ) < W.p := by omega
      have p1 : 0 < W.u1 τ a - W.u1 τ b := by
        by_contra! hc
        nlinarith
      have p2 : 0 < W.u1 τ a - W.u1 τ b - 3 * N := by
        by_contra! hc
        nlinarith
      refine ⟨by omega, ?_⟩
      simp only [Wts.u', ite_eq_left ha', ite_eq_right ha]
      omega
    · have e := g1 hb
      have hN : (0 : ℤ) ≤ W.T + W.Dd + 2 + 2 * N := by positivity
      refine ⟨by omega, ?_⟩
      simp only [Wts.u']
      by_cases ha : (a : ℕ) < W.p
      · have hb' : (b : ℕ) < W.p := by omega
        rw [ite_eq_left ha, ite_eq_left hb']; omega
      · have hb' : ¬ (b : ℕ) < W.p := by omega
        rw [ite_eq_right ha, ite_eq_right hb']; omega
  have s1 : StrictAnti (W.u1 τ) := strictAnti_of_step _ fun a b h => (step a b h).1
  exact ⟨s1, strictAnti_of_step _ fun a b h => (step a b h).2,
    (Int.cast_strictMono (R := ℝ)).comp_strictAnti s1⟩

end GlobalTheory.MeanTop
