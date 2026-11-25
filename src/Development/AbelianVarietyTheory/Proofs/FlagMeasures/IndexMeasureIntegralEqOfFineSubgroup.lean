module

import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInvariantIntegralMatrixMul
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumRefine

@[expose] public section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt

open scoped Pointwise Classical in
open Function in
open scoped Pointwise Classical in
open Function in
open scoped Pointwise Classical in
open Function in
private lemma finsum_quotient_out_eq_relIndex_mul_of_le {W : Type} [AddCommGroup W] {C B : AddSubgroup W} (hCB : C ≤ B)
    (hidx : C.relIndex B ≠ 0) (φ : W → ℂ) (hinv : ∀ w b : W, b ∈ B → φ (w + b) = φ w)
    (hφ : ((fun w : W => (w : W ⧸ B)) '' support φ).Finite) :
    ∑ᶠ c : W ⧸ C, φ (Quotient.out c) = (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ (Quotient.out c) := by
  apply _root_.GlobalTheory.SW.LinChange.finsum_quot_le <;> assumption

open scoped Pointwise Classical in
open Function in
private lemma finsum_out_div_relIndex_eq_of_le {W : Type} [AddCommGroup W] {A B C : AddSubgroup W}
    {φ : W → ℂ} (hB : _root_.GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hC : C.relIndex A ≠ 0) :
    (∑ᶠ c : W ⧸ C, φ (Quotient.out c)) / (C.relIndex A : ℂ) =
      (∑ᶠ c : W ⧸ B, φ (Quotient.out c)) / (B.relIndex A : ℂ) := by
  obtain ⟨hBA, -, hinv, hsupp⟩ := hB
  have hidx : C.relIndex B ≠ 0 := by
    rw [← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA] at hC
    exact left_ne_zero_of_mul hC
  rw [finsum_quotient_out_eq_relIndex_mul_of_le hCB hidx φ hinv hsupp, ← AddSubgroup.relIndex_mul_relIndex C B A hCB hBA,
    Nat.cast_mul, mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hidx)]


open scoped Pointwise Classical in
open Function in
theorem _root_.GlobalTheory.IdxInt.cint_eq_of_fine : ∀ {W : Type} [AddCommGroup W] (A B : AddSubgroup W) (φ : W → ℂ),
    _root_.GlobalTheory.IdxInt.Fine A φ B → _root_.GlobalTheory.IdxInt.cint A φ = (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) := by
  intro W _ A B φ hB
  have h : _root_.GlobalTheory.IdxInt.Nice A φ := ⟨B, hB⟩
  unfold _root_.GlobalTheory.IdxInt.cint
  rw [dite_eq_left h]
  have hB0 := h.choose_spec
  have hidx : (B ⊓ h.choose).relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hB.2.1 hB0.2.1
  rw [← finsum_out_div_relIndex_eq_of_le hB0 inf_le_right hidx, finsum_out_div_relIndex_eq_of_le hB inf_le_left hidx]

end GlobalTheory.IdxInt
