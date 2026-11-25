module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleLawAdd
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.LowLaw

theorem eq_single_of_degree_eq_one {σ : Type} {e : σ →₀ ℕ} (h : e.degree = 1) :
    ∃ j, e = Finsupp.single j 1 := by
  classical
  have hne : e ≠ 0 := by rintro rfl; simp at h
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hle : Finsupp.single j 1 ≤ e := by
    rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  refine ⟨j, ?_⟩
  have hsum : e = (e - Finsupp.single j 1) + Finsupp.single j 1 := (tsub_add_cancel_of_le hle).symm
  have hd : (e - Finsupp.single j 1).degree = 0 := by
    have h2 := congrArg Finsupp.degree hsum
    rw [map_add (f := _), Finsupp.degree_single, h] at h2
    omega
  rw [Finsupp.degree_eq_zero_iff] at hd
  rw [hsum, hd, zero_add]

theorem coeff_addLaw (R : Type) [CommRing R] (d : ℕ) (i : Fin d) (α : Fin d ⊕ Fin d →₀ ℕ) :
    coeff α (addLaw R d i) =
      if α = Finsupp.single (Sum.inl i) 1 ∨ α = Finsupp.single (Sum.inr i) 1 then 1 else 0 := by
  classical
  simp only [addLaw, map_add (f := _), coeff_X]
  by_cases h1 : α = Finsupp.single (Sum.inl i) 1
  · have h2 : α ≠ Finsupp.single (Sum.inr i) 1 := by
      rw [h1]; intro h
      exact Sum.inl_ne_inr ((Finsupp.single_left_inj one_ne_zero).1 h)
    rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left (Or.inl h1), add_zero]
  · rw [ite_eq_right h1, zero_add]
    by_cases h2 : α = Finsupp.single (Sum.inr i) 1
    · rw [ite_eq_left h2, ite_eq_left (Or.inr h2)]
    · rw [ite_eq_right h2, ite_eq_right (by tauto)]

variable {k : Type} [CommRing k] {d : ℕ}

theorem coeff_inl {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inl j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have hu := congrArg (coeff (Finsupp.single j 1)) (congrFun h.unit i)
  simp only [op, at2] at hu
  rw [GlobalTheory.FormalCalc.coeff_single_subst (fun s => by cases s <;> simp), Fintype.sum_sum_type] at hu
  simpa [coeff_X, Finsupp.single_left_inj] using hu

theorem coeff_inr {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inr j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have hc := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) (h.comm i)
  simp only [swap, at2] at hc
  rw [GlobalTheory.FormalCalc.coeff_single_subst (fun s => by cases s <;> simp), Fintype.sum_sum_type] at hc
  rw [← hc, ← coeff_inl h i j]
  simp [coeff_X, Finsupp.single_left_inj]

end GlobalTheory.Katz.LowLaw

namespace GlobalTheory.Katz


open LowLaw in
theorem coeff_law_of_degree_le_one (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ)
    (i : Fin d) (α : Fin d ⊕ Fin d →₀ ℕ) (hα : α.degree ≤ 1) :
    coeff α (μ i) = coeff α (addLaw k d i) ∧
      coeff α (Katz.lift p (μ i)) = coeff α (addLaw (Fr p k) d i) := by
  classical
  have h1 : coeff α (μ i) = coeff α (addLaw k d i) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hα with h0 | h1
    · rw [(Finsupp.degree_eq_zero_iff α).1 h0, coeff_zero_eq_constantCoeff_apply, h.const,
        coeff_addLaw, ite_eq_right]
      rintro (h | h) <;> exact Finsupp.single_ne_zero.2 one_ne_zero h.symm
    · obtain ⟨s, rfl⟩ := eq_single_of_degree_eq_one h1
      rcases s with j | j
      · rw [coeff_inl h, coeff_addLaw]; simp [Finsupp.single_left_inj]
      · rw [coeff_inr h, coeff_addLaw]; simp [Finsupp.single_left_inj]
  refine ⟨h1, ?_⟩
  rw [coeff_lift, h1, coeff_addLaw, coeff_addLaw]
  split_ifs <;> simp

end GlobalTheory.Katz
