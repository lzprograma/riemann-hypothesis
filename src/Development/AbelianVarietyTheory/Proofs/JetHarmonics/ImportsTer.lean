module

public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsThetaFrame
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiWeightZeroProduct
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValFinProdGen
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

namespace GlobalTheory.PowThetaFrame

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ThetaFrameF := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c n T io y _ C P _ g g' _ hg' _ _ _ π π' _ hπ' _ _ _ F _ _ _ _ _ _ v ϖ hϖ hv
    Q hQ D' A' G' _ _ pD pA pG U' PU _ oD' hx hact
  let _ := H.starRing
  obtain ⟨θ, hν, hθ⟩ := exists_thetaFrame hL hL2 hL4 hT T.V ϖ hϖ D' (sumQ pD.xe Q)
    (QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) F v hv
  have hw : TraceFormTwistIso D'.toPre oD' H.w0 :=
    PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E) (fun a x => funext (hx a x)) P.oD oD' hact H.w0 P.w0
  obtain ⟨f, -, hf⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw (star π') g' 1 hg'.one_le le_rfl
    (by rw [star_star, mul_comm]; exact hπ')
  exact ⟨θ, f θ, hν, hθ, (hf _ _).2 rfl⟩

end GlobalTheory.PowThetaFrame
