module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem plOf_bijective_card (D : D7) :
    Function.Bijective (plOf D) ∧ Fintype.card D.what₂.Tau = D.R.f := by
  refine ⟨?_, D.what₂.card_Tau⟩
  have hb := D.R.toFrame.iota_bijective
  refine D.eTau.symm.bijective.comp (f := fun z : RPl D.R =>
    (if z.1 then ⟨D.R.tau2 z.2, rfl⟩ else ⟨D.R.tau1 z.2, rfl⟩ : D.R.Psi)) ⟨?_, ?_⟩
  · rintro ⟨a, s⟩ ⟨b, t⟩ h
    have h' := congrArg Subtype.val h
    cases a <;> cases b <;>
      simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, Bool.false_eq_true, ite_true, ite_false, Prod.mk.injEq] at h'
    · exact Prod.ext rfl (hb.1 h'.2)
    · exact absurd h'.1.1 (by decide)
    · exact absurd h'.1.1 (by decide)
    · exact Prod.ext rfl (hb.1 h'.2)
  · rintro ⟨⟨⟨a, b⟩, h⟩, hg⟩
    obtain ⟨t, rfl⟩ := hb.2 h
    have hb1 : b = 1 := hg
    subst hb1
    rcases Int.units_eq_one_or a with rfl | rfl
    · exact ⟨(false, t), rfl⟩
    · exact ⟨(true, t), rfl⟩

end GlobalTheory.RunDepth
