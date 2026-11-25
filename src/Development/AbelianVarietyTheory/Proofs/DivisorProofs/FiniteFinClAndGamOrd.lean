module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GamOrdNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SublevelSplitting
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

namespace GlobalTheory.FunObj.ClassFin

variable {D : D7}

def gfcToGf (V : HSp D) : GfC V →* Bridge.Gf V := (finHom V).rangeRestrict.comp (GfC V).subtype

theorem gfcToGf_surjective (V : HSp D) : Function.Surjective (gfcToGf V) := by
  apply GlobalTheory.FunObj.gfcToGf_surjective

theorem finG_injective (V : HSp D) : Function.Injective (finG V) := by
  apply GlobalTheory.FunObj.finG_injective

theorem finite_finCl_and_gamOrd : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))),
    (∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef) → IsCO V K → Finite (FinCl V K) ∧ ∀ x, gamOrd V K x ≠ 0 := by
  apply GlobalTheory.FunObj.finite_finCl_and_gamOrd

end GlobalTheory.FunObj.ClassFin
