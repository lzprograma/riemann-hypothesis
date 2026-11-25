module

public import Formalism.LocalToGlobal.ProjectiveLattices.CurveOpen
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValues
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
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem cusp_eq_zero_of_generic_values {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hG : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (g : Rul Xo c) (hg : g ∈ cusp Xo c U a n) (h0 : ∀ Z, evC hG Z g = 0) : g = 0 := by
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  exact sec_eq_zero_of_generic_values E H Dw l Xo c hL hG (hA hG) a n g (cusp_le_sec Xo c U a n hg) h0




theorem genValInj_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (_ : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), GenValInjSt h j hG := by
  intro D T h j _ hG w g h0
  have hg : (g : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := cutR_le T.C j w g.2
  exact Subtype.ext (cusp_eq_zero_of_generic_values (T.Q.Xo j) T.Q.c (T.U j) hG (wtA w) w.n _ hg h0)

end GlobalTheory.Reg
