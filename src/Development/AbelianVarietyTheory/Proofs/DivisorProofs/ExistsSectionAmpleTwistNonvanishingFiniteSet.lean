module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem exists_sec_finite_subset_nonzeroLocus : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M A : HermLB p), IsAmpleLB A.B → ∀ S : Set X, S.Finite → ∃ b : ℕ, 0 < b ∧ ∃ u : (M.tens (A.pow b)).B.Sec, S ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p D hX M A hA S hS
  have := hX.isLocallyNoetherian
  have hEv : ∀ᶠ b : ℕ in atTop, ∀ (N : LB X) (hN : N.IsLB),
      CechPic.cls N hN = CechPic.cls M.B M.isLB + (b : ℤ) • CechPic.cls A.B hA.isLB →
        ∃ u : N.Sec, S ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u :=
    tendsto_natCast_atTop_atTop.eventually
      (hA.eventually_exists_finite_subset_nonzeroLocus M.isLB hS)
  obtain ⟨b, h₁, hb⟩ := (hEv.and (eventually_gt_atTop 0)).exists
  refine ⟨b, hb, ?_⟩
  have eA : CechPic.cls _ (A.pow b).isLB = (b : ℤ) • CechPic.cls A.B hA.isLB :=
    (CechPic.cls_lbPow hA.isLB b (A.pow b).isLB).trans (natCast_zsmul _ _).symm
  obtain ⟨u, hu⟩ := h₁ _ (M.tens (A.pow b)).isLB
    ((CechPic.cls_tens M.isLB (A.pow b).isLB (M.tens (A.pow b)).isLB).trans (congrArg _ eA))
  exact ⟨u, hu⟩

end GlobalTheory.VolBr
