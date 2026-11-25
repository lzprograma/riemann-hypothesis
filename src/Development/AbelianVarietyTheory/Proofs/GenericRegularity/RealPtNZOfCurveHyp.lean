module

public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CountQAtStGenericSectionPrimes
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliExistenceAndModuliScheme
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralFramesModelInvertiblePushforward
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NatCastMemMaximalIdealOfOverLa
public import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
public import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPf
public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtMain
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



open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory



theorem realPtNZ_of_curveHyp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (_ : GenFromTest (T.Q.Xo j) T.Q.c hG) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → 0 < wL.n → ∀ (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ], RealPtNZSt h j hj hG G la hU := by
  intro D T h j hj hG hT ka wL wF G S g0 la hH hV _ hB hwL hU _
  obtain ⟨-, hbc, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hany, htw, -, -⟩ := GlobalTheory.lawsFieldsSeparately
  obtain ⟨hgood, -, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨hpq, hr, -⟩ := hnum j hj
  have := CompFin.finite_comp (T.Q.Xo j) T.Q.c
  obtain ⟨-, -, -, hWt, -⟩ := GlobalTheory.Frames.algebraic_laws hbc _ _ _ _ (T.Q.Xo j) T.Q.c
  exact realPt_of h j hj hG G la hU hwL
    (ptOfS_of h j hj hG hany htw hT hV G hB la (GlobalTheory.SecCount.countQAtSt D T h j hj hG hT ka wL wF G S g0 la hH)) hT
    (GlobalTheory.intFrames_of_laws hbc htw _ _ _ _ (T.Q.Xo j) T.Q.c) hWt
    (GlobalTheory.Frames.modelAtSt_of_good GlobalTheory.Moduli.jointExistence_and_moduliScheme.1 GlobalTheory.Moduli.jointExistence_and_moduliScheme.2 _ _ _ _ (T.Q.Xo j) T.Q.c (hpq ▸ hr) hgood la)

end GlobalTheory
