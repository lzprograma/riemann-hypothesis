module

public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.DepthRule

theorem depth_le_scaled_value : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), w.LastPos → ∀ (s : 𝓞 (recB h.toLawsCore).KO), s ≠ 0 → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtA j la), ∀ f ∈ T.th j w, (recPJ h j hj).depth s w la y ≤ (((vLa la ((s : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) : EReal) + vAtV y f := by
  intro D T h j hj w hw s hs la y f hf
  have hc : f ∈ cutR T.C j w := by
    rw [cutR_eq T.C hj]
    exact h.thCusp j hj _ _ (dom_wtA w) (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj _ hw) f hf
  have hsK : ((s : 𝓞 T.Q.c.F) : T.Q.c.F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hs
  let F : (recB h.toLawsCore).Cusp j w := ⟨f, hc⟩
  have hF : F ∈ (recPJ h j hj).thAll w := Submodule.subset_span hf
  have hsF : s • F ∈ (recPJ h j hj).WWc s w := ⟨F, hF, rfl⟩
  refine (iInf₂_le (s • F) hsF).trans (le_of_eq ?_)
  rw [recPJ_vAt_inc h j hj la y w (s • F)]
  have h1 : (s • F).1 = ((s : 𝓞 T.Q.c.F) : T.Q.c.F) • f := rfl
  rw [h1]
  exact vAtV_smul y _ f hsK

end GlobalTheory.DepthRule
