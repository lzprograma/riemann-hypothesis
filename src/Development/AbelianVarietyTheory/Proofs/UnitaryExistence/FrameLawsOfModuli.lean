module

public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
public import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AlgebraicPointsModuliEveryPlace
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntAll
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntFrExtOfGoodLevel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralLatticeStructureUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsNumberFieldPoint
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridgeU
public import Formalism.LocalToGlobal.ProjectiveLattices.ReadLeaves
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

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology

namespace GlobalTheory.Exist

theorem frame_laws_of_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (ChartCoverF Xo c ∧ FrChartF Xo c ∧ BorChartF Xo c ∧ IntLatU Xo c ∧ AllTest Xo c ∧ ∀ σ : c.F →+* ℂ, BCEx Xo c σ ∧ WtC Xo c σ) ∧ (1 ≤ Dw.p + Dw.q → Nonempty Xo.X ∧ AlgPtLa Xo c ∧ ((∀ p : ℕ, p.Prime → l.GoodAt p) → IntFrExt Xo c ∧ IntAll Xo c)) := by
  intro E _ _ _ H Dw l Xo c
  have hL := GlobalTheory.lawsFieldsSeparately
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := hL.2.1
  have hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt := hL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hC := GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c
  have hA := GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c
  have hN : N1c := GlobalTheory.closing_of_abelianSchemeLaws
  refine ⟨⟨hC, frChartF_of hC, borChartF_of_cover hC, GlobalTheory.Frames.intLatU_holds E H Dw l Xo c, hA,
    fun σ => ⟨fun p y ψ => ?_, wtC_of (borChartF_of_cover hC) hA σ⟩⟩, fun hpq => ⟨?_,
    GlobalTheory.algPtLa_moduli hN E H Dw l Xo c hpq, fun hg => ⟨?_, ?_⟩⟩⟩
  · exact GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ ψ y
  · obtain ⟨L, _, _, j, x, -⟩ := GlobalTheory.moduli_exists_numberField_point hN E H Dw l Xo c hpq
    exact ⟨x (IsLocalRing.closedPoint L)⟩
  · exact GlobalTheory.Exist.intFrExt_of_good GlobalTheory.partI_closed GlobalTheory.Moduli.moduli_scheme_exists hS hT
      E H Dw l Xo c hpq hg
  · exact (Formalism.L2.PjFree.intAll_iff Xo c).1 (GlobalTheory.IntegralFrames.intAll GlobalTheory.partI_closed
      GlobalTheory.Moduli.moduli_scheme_exists hS hT E H Dw l Xo c hpq hg)

end GlobalTheory.Exist
