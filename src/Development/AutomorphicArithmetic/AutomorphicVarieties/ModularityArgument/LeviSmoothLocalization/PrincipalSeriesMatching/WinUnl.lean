module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Formalism.DoubleCosetMeasures.Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Lemma
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

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.Z.Gam
open scoped Classical

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

private lemma quot_ne (q : ℕ) (hq : q ≠ 0) (t : ℝ) (a b : ℂˣ)
    (h1 : ‖(a : ℂ)‖ < (q : ℝ) ^ (t + 1 / 2)) (h2 : (q : ℝ) ^ (t - 1 / 2) < ‖(b : ℂ)‖) :
    ((a * b⁻¹ : ℂˣ) : ℂ) ≠ q := by
  intro h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hb : (b : ℂ) ≠ 0 := b.ne_zero
  have ha : (a : ℂ) = q * b := by
    rw [← h, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have hn : ‖(a : ℂ)‖ = q * ‖(b : ℂ)‖ := by
    rw [ha, norm_mul, Complex.norm_natCast]
  have hsplit : (q : ℝ) ^ (t + 1 / 2) = q * (q : ℝ) ^ (t - 1 / 2) := by
    rw [show t + 1 / 2 = 1 + (t - 1 / 2) by ring, Real.rpow_add hq0, Real.rpow_one]
  rw [hn, hsplit] at h1
  exact absurd (lt_of_mul_lt_mul_left h1 hq0.le) (not_lt.mpr h2.le)

theorem winUnl : WinUnl := by
  intro K _ _ _ n π t v hw s hs ξ hξ ξ' hξ' _
  have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact quot_ne _ hq t _ _ (hw.2 s hs ξ hξ).2 (hw.2 s hs ξ' hξ').1

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
