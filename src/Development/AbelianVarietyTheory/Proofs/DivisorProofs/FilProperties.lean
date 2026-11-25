module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
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
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal

@[expose] public section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory.PDA

theorem map_fil_le {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {C : Type} [CommRing C]
    {J' : Ideal C} (δ' : DividedPowers J') (f : B →+* C) (hf : IsDPMorphism δ δ' f) (N : ℕ) :
    (fil δ N).map f ≤ fil δ' N := by
  apply _root_.FubiniStudyChowHeightFormula₂.Adr.Fil.map_fil_le <;> assumption

theorem fil_properties : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J), fil δ 0 = ⊤ ∧ fil δ 1 = J ∧ (∀ m n, m ≤ n → fil δ n ≤ fil δ m) ∧ (∀ m n, fil δ m * fil δ n ≤ fil δ (m + n)) ∧ (∀ n, ∀ x ∈ J, δ.dpow n x ∈ fil δ n) ∧ (IsNilDP δ ↔ ∃ N, IsLev δ N) ∧ ∀ (C : Type) [CommRing C] (J' : Ideal C) (δ' : DividedPowers J') (f : B →+* C), IsDPMorphism δ δ' f → ∀ N, (fil δ N).map f ≤ fil δ' N := by
  intro B _ J δ
  refine ⟨fil_zero_eq_top δ, fil_one_eq δ, fun m n h ↦ GlobalTheory.Cris.ExpBij.dpFil_anti δ h, fun m n ↦ ?_,
    fun n x hx ↦ GlobalTheory.Cris.ExpBij.dpow_mem_dpFil δ hx n, isDPNilpotent_iff_exists_isLevel δ,
    fun C _ J' δ' f hf N ↦ map_fil_le δ δ' f hf N⟩
  rw [Ideal.mul_le]
  exact fun a ha b hb ↦ GlobalTheory.Cris.ExpBij.mul_mem_dpFil δ ha hb

end GlobalTheory.PDA
