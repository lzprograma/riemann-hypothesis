module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtLAlgebraMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open GlobalTheory.LogDerProj

noncomputable section

namespace GlobalTheory.LogDerProj

theorem exists_pow_smul_eq_of_res_eq {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R)
    [IsLocalization.Away f S] (φ : k →+* R) (hφ : φ.FiniteType) (J : Ideal R) (D₁ D₂ : logSub φ J)
    (h : res (S := S) f φ J D₁ = res (S := S) f φ J D₂) : ∃ c : Submonoid.powers f, c • D₁ = c • D₂ := by
  classical
  set E : Derivation ℤ R R := D₁.1 - D₂.1 with hE
  have hloc : ∀ r, ∃ m : Submonoid.powers f, (m : R) * E r = 0 := by
    intro r
    have h1 := congrArg (fun D => D.1 (algebraMap R S r)) h
    simp only [res_apply] at h1
    have h2 : algebraMap R S (E r) = 0 := by
      rw [hE, Derivation.sub_apply, map_sub, h1, sub_self]
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f) S _).1 h2
  choose m hm using hloc
  letI := φ.toAlgebra
  have hft : Algebra.FiniteType k R := hφ
  obtain ⟨s, hs⟩ := hft.out
  let c : Submonoid.powers f := ∏ x ∈ s, m x
  have hcs : ∀ x ∈ s, (c : R) * E x = 0 := by
    intro x hx
    have : (c : R) = (∏ y ∈ s.erase x, m y : Submonoid.powers f) * m x := by
      simp only [c]
      rw [← Submonoid.coe_mul, ← Finset.prod_erase_mul s m hx]
    rw [this, mul_assoc, hm x, mul_zero]
  have hall : ∀ r, (c : R) * E r = 0 := by
    intro r
    have hr : r ∈ Algebra.adjoin k (s : Set R) := by rw [hs]; trivial
    induction hr using Algebra.adjoin_induction with
    | mem x hx => exact hcs x hx
    | algebraMap a =>
      have e1 : D₁.1 (φ a) = 0 := D₁.2.1 a
      have e2 : D₂.1 (φ a) = 0 := D₂.2.1 a
      show (c : R) * E (φ a) = 0
      rw [hE, Derivation.sub_apply, e1, e2, sub_self, mul_zero]
    | add x y _ _ hx hy => rw [map_add (f := _), mul_add, hx, hy, add_zero]
    | mul x y _ _ hx hy =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add]
      calc (c : R) * (x * E y) + (c : R) * (y * E x) = x * ((c : R) * E y) + y * ((c : R) * E x) := by ring
        _ = 0 := by rw [hx, hy, mul_zero, mul_zero, add_zero]
  refine ⟨c, ?_⟩
  apply Subtype.ext
  ext r
  rw [Submonoid.smul_def, Submonoid.smul_def]
  show ((c : R) • D₁.1) r = ((c : R) • D₂.1) r
  rw [Derivation.smul_apply, Derivation.smul_apply, smul_eq_mul, smul_eq_mul, ← sub_eq_zero, ← mul_sub]
  have := hall r
  rwa [hE, Derivation.sub_apply] at this

end GlobalTheory.LogDerProj
