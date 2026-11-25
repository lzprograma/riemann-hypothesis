module

public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.L2.DIV

namespace GlobalTheory.IdemChar


open Classical in
theorem sum_coeff_chiIdem_mul {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
    {φ χ : G → K} (hφ : IsAbsIrrChar φ) (hχ : IsAbsIrrChar χ) :
    ∑ g : G, (chiIdem φ).coeff g * χ g = if φ = χ then χ 1 else 0 := by
  have hG : (Fintype.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero

  have hc := conv_char hχ hφ 1
  have hre : ∑ s : G, χ s⁻¹ * φ (s * 1) = ∑ g : G, φ g⁻¹ * χ g :=
    Fintype.sum_equiv (Equiv.inv G) _ _ (fun s => by simp [mul_comm])
  rw [hre] at hc
  have hsum : ∑ g : G, (chiIdem φ).coeff g * χ g
      = ((∑ g : G, φ g⁻¹ * χ g) * φ 1) / (Fintype.card G : K) := by
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [coeff_chiIdem]
    ring
  rw [hsum, hc]
  by_cases h : φ = χ
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, mul_div_cancel_left₀ _ hG]
  · have h' : ¬ χ = φ := fun e => h e.symm
    rw [ite_eq_right h', ite_eq_right h, zero_div]

theorem sum_coeff_idemOf_mul : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K)), (∀ χ ∈ X, IsAbsIrrChar χ) → ∀ χ ∈ X, ∑ g : G, (idemOf X).coeff g * χ g = χ 1 := by
  intro K _ _ G _ _ X hX χ hχ
  classical
  calc ∑ g : G, (idemOf X).coeff g * χ g
      = ∑ g : G, ∑ ψ ∈ X, (chiIdem ψ).coeff g * χ g := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [coeff_idemOf, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [coeff_chiIdem]
    _ = ∑ ψ ∈ X, ∑ g : G, (chiIdem ψ).coeff g * χ g := Finset.sum_comm
    _ = ∑ ψ ∈ X, if ψ = χ then χ 1 else 0 :=
        Finset.sum_congr rfl fun ψ hψ => sum_coeff_chiIdem_mul (hX ψ hψ) (hX χ hχ)
    _ = χ 1 := by simp [hχ]

end GlobalTheory.IdemChar
