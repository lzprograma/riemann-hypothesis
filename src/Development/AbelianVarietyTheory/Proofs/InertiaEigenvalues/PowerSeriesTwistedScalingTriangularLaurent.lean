module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open GlobalTheory.NL

namespace GlobalTheory.NL.Twist

variable {L M : Type} [Field L] [TopologicalSpace L] [AddCommGroup M] [Module L M]

theorem conv_mem_of_forall (w : PowerSeries L) (g : ℤ → M) (S : Submodule L M) (j : ℤ)
    (h : ∀ i : ℕ, g (j - i) ∈ S) : conv w g j ∈ S := by
  unfold conv
  exact finsum_induction (· ∈ S) S.zero_mem (fun _ _ => S.add_mem)
    (fun i => S.smul_mem _ (h i))

theorem conv_eq_sum (w : PowerSeries L) (g : ℤ → M) (m : ℤ) (hg : ∀ j < m, g j = 0) (k : ℤ) :
    conv w g k = ∑ i ∈ Finset.range ((k - m).toNat + 1), PowerSeries.coeff i w • g (k - i) := by
  unfold conv
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Function.mem_support] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra! hc
  apply hi
  have : g (k - i) = 0 := hg _ (by omega)
  simp [this]

theorem tri (w : PowerSeries L) (u : L) (Sub : ℤ → Submodule L M) (hSub : Monotone Sub) (y : ℕ)
    (f : ℤ → M) (hf : ∃ m : ℤ, ∀ j < m, f j = 0) (hfS : ∀ j, f j ∈ Sub j) (k : ℤ)
    (hk : ∀ j < k, f j ∈ Sub (j - y)) :
    (∃ m : ℤ, ∀ j < m, conv w (fun m => u ^ m • f m) j = 0) ∧
    (∀ j, conv w (fun m => u ^ m • f m) j ∈ Sub j) ∧
    (∀ j < k, conv w (fun m => u ^ m • f m) j ∈ Sub (j - y)) ∧
    conv w (fun m => u ^ m • f m) k - (PowerSeries.constantCoeff w * u ^ k) • f k ∈ Sub (k - y) := by
  obtain ⟨m, hm⟩ := hf
  have hg : ∀ j < m, (fun m => u ^ m • f m) j = 0 := fun j hj => by simp [hm j hj]
  refine ⟨⟨m, fun j hj => ?_⟩, fun j => ?_, fun j hj => ?_, ?_⟩
  · refine (Submodule.mem_bot L).1 (conv_mem_of_forall w _ ⊥ j (fun i => ?_))
    rw [hm _ (by omega), smul_zero]
    exact Submodule.zero_mem _
  · exact conv_mem_of_forall w _ _ j (fun i =>
      Submodule.smul_mem _ _ (hSub (by omega : j - (i : ℤ) ≤ j) (hfS _)))
  · exact conv_mem_of_forall w _ _ j (fun i =>
      Submodule.smul_mem _ _ (hSub (by omega : j - (i : ℤ) - y ≤ j - y) (hk _ (by omega))))
  · rw [conv_eq_sum w _ m hg k, Finset.sum_range_succ']
    have h0 : PowerSeries.coeff 0 w • (u ^ (k - ((0 : ℕ) : ℤ)) • f (k - ((0 : ℕ) : ℤ))) -
        (PowerSeries.constantCoeff w * u ^ k) • f k = 0 := by
      simp [mul_smul]
    rw [add_sub_assoc, h0, add_zero]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_))
    exact hSub (by omega : k - ((i + 1 : ℕ) : ℤ) - y ≤ k - y) (hk _ (by omega))

end GlobalTheory.NL.Twist
