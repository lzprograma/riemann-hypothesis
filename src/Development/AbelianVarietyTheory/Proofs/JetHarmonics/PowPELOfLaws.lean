module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivPointsOfIsPowGrp
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPelUnifOfUnifPow
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValFinProdGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTripleStatement
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem powPEL_of_laws : Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → PowPELF := by
  intro h₁ h₂ h₃ h₄ h₅ hT E _ _ _ H Dw l Xo c n T io y _ C P _ g g' _ _ _ _ _ π π' _ _ _ _ _ F _ _ _ _ _ _ v ϖ hϖ _ I Q hQ
    D' A' G' _ _ pD pA pG U' PU _ oD' hx hB
  letI := H.starRing
  have hA : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨oA', hoA, t', P', hP'⟩ :=
    GlobalTheory.exists_pelUnif_of_unifPow h₁ h₂ h₄ hT T.V E H C.I.G P n D' A' G' pD pA pG U' PU oD' hx hB
  refine ⟨oA', hoA, GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ,
    GlobalTheory.exists_tateIso_of_isPowPolAV h₁ h₂ h₄ hT E H T.V n P.A A' pA F _ _ hoA Dw I, t', P', ?_, hP'⟩
  exact GlobalTheory.T.torsionIso_of_linear_uniformisation_triple ⟨h₁, h₂, h₃, h₄, h₅⟩ (twistBCSpan_of hT) GlobalTheory.RatioVal.main
    (GlobalTheory.twisting_statements_of_laws h₁ hT).1 (GlobalTheory.UnitBallFree.main h₁.globalFns hT) E H T.V _ hA t' P'

end GlobalTheory.PowGerm
