module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

@[expose] public section

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

theorem smoothOfRelativeDimension_powObj {S : Scheme.{0}} (G : Over S) (g : ℕ)
    (hG : SmoothOfRelativeDimension g G.hom) : ∀ n : ℕ, SmoothOfRelativeDimension (n * g) (powObj G n).hom
  | 0 => by
    have h : SmoothOfRelativeDimension 0 (𝟙 S) := inferInstance
    rw [Nat.zero_mul]
    exact h
  | n + 1 => by
    have ih := smoothOfRelativeDimension_powObj G g hG n
    have h1 : SmoothOfRelativeDimension (n * g) (pullback.fst G.hom (powObj G n).hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _).flip ih
    have h2 : SmoothOfRelativeDimension (n * g + g) (pullback.fst G.hom (powObj G n).hom ≫ G.hom) :=
      inferInstance
    rw [Nat.succ_mul]
    exact h2

theorem polAV_g_of_isPowPolAV : ∀ (K : Type) [Field K] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of K))),
    IsPowPolAV A' A j → A'.g = j * A.g := by
  intro K _ j A A' p
  let e : A'.A ≅ powObj A.A j := p.lim.conePointUniqueUpToIso (powIsLimit A.A j)
  have hw : A'.A.hom = e.hom.left ≫ (powObj A.A j).hom := (Over.w e.hom).symm
  have h1 := smoothOfRelativeDimension_powObj A.A A.g A.smoothDim j
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h2 : SmoothOfRelativeDimension (0 + j * A.g) A'.A.hom := by
    rw [hw]; infer_instance
  have := H1.dim_unique _ A'.smoothDim h2 (eSec A'.A (default : PrimeSpectrum K))
  simpa using this

end GlobalTheory
