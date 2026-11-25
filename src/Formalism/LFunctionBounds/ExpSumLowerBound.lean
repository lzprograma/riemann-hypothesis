module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.MulChar.Duality
public import Formalism.StatementOC
import Mathlib.RingTheory.SimpleRing.Principal

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LFunctionBounds.Statement, Formalism.LFunctionBounds.ExpSumLowerBound

-- ===== clump member: Formalism.LFunctionBounds.Statement =====
-- clump-header: {"m": "Formalism.LFunctionBounds.Statement", "h": "module\n\npublic import Mathlib.NumberTheory.LSeries.DirichletContinuation\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\npublic import Mathlib.NumberTheory.MulChar.Duality\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex

noncomputable section

namespace Formalism.FX

open Classical

def triples (l : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 l ×ˢ Finset.Icc 1 l ×ˢ Finset.Icc 1 l).filter (fun S => S.1 + S.2.1 + S.2.2 = l)

def W (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ S ∈ triples l, ν S *
    ((if S.1 = x then 1 else 0) + (if S.2.1 = x then 1 else 0) + (if S.2.2 = x then 1 else 0))

def Snu (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) (χ : DirichletCharacter ℂ l) : ℂ :=
  ∑ x ∈ Finset.Ioo 0 l, (W l ν x : ℂ) * (starRingEnd ℂ) (χ (x : ZMod l))

def cW (l : ℕ) [NeZero l] (ν : ℕ × ℕ × ℕ → ℝ) (χ : DirichletCharacter ℂ l) : ℂ :=
  DirichletCharacter.LFunction χ 0 * Snu l ν χ / ((((l : ℝ) - 1) / 2 : ℝ) : ℂ)

end Formalism.FX
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LFunctionBounds.Statement =====

-- ===== clump member: Formalism.LFunctionBounds.ExpSumLowerBound =====
-- clump-header: {"m": "Formalism.LFunctionBounds.ExpSumLowerBound", "h": "module\n\npublic import Formalism.LFunctionBounds.Statement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex

noncomputable section

namespace Formalism.FX

open Classical

def rectInt (g : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) : ℂ :=
  (∫ x in x0..x1, g (x + y0 * I)) - (∫ x in x0..x1, g (x + y1 * I)) +
    I * (∫ y in y0..y1, g (x1 + y * I)) - I * (∫ y in y0..y1, g (x0 + y * I))

def RectResidue : Prop :=
  ∀ (g G : ℂ → ℂ) (P : Finset ℂ) (b : ℂ → ℂ) (x0 x1 y0 y1 : ℝ), x0 < x1 → y0 < y1 →
    (∀ p ∈ P, x0 < p.re ∧ p.re < x1 ∧ y0 < p.im ∧ p.im < y1) →
    (∃ U : Set ℂ, IsOpen U ∧ (Set.uIcc x0 x1 ×ℂ Set.uIcc y0 y1) ⊆ U ∧ DifferentiableOn ℂ G U) →
    (∀ w : ℂ, w ∉ P → g w = G w + ∑ p ∈ P, b p / (w - p)) →
    rectInt g x0 x1 y0 y1 = 2 * Real.pi * I * ∑ p ∈ P, b p

end Formalism.FX
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LFunctionBounds.ExpSumLowerBound =====
