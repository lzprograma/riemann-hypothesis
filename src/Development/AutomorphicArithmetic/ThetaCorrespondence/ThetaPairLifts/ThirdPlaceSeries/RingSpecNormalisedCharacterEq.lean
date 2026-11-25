module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalLinkChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LiftToGlobalDescentData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
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



section
noncomputable section
namespace GlobalTheory.HeightCounting
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.L2 Formalism.L2.NT

structure NAllCAlt (D : D7) (C : NChoice D) where
  gal : _root_.Formalism.L2.NGalTiedAlt D
  cover : NormalizedLocalCompatibility D gal.mt
  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD
  types : NormalizedTypesCompatibility D gal.fr.jE
  twF : TwFrame D
  tw : NTwTied D twF
  nct : NChTie D C
  exp : NExpTied D
  choice : ChoiceC D C
  cf : Host.CharFrame D
  tp : Host.TupTied D cf C
  plB : D.what₂.places.Pl → ValuationSubring ℂ
variable {D : D7} {C : NChoice D} {I : TwIn D}
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
structure ArchimedeanComparison' (hL : _root_.UpperTheory.Zero.LLC.RecTExists) : Prop where
  pht : PhtCmp
end GlobalTheory.HeightCounting
end
end
