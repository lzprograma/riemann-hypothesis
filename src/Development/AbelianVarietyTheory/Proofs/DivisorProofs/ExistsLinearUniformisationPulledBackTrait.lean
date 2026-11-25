module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SystemPrimesDistinctLevelsGeThree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationBaseChangeCompleteDvr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.TraitPull

theorem exists_pull_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ h : T.V →+* W, Function.Injective h → IsLocalHom h → ∃ (tW : SAB H (Sp W)) (_ : SABMap tW T.t (spMap h)) (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X), ∀ y, 0 ≤ T.be (e y) (e y) ∧ ∃ r, PsiCoord PW.D.toPre y r ∧ Associated (r ^ 2) (h T.ϖ ^ (T.be (e y) (e y)).toNat) := by
  intro E _ _ _ H Dw l Xo c T W _ _ _ hW hWd h hi hl
  obtain ⟨tW, ⟨m⟩⟩ := GlobalTheory.Models.Inhab.exists_pull (spMap h) T.t
  obtain ⟨PW, e, he⟩ := GlobalTheory.UnifDvrBaseChange.exists_pelUnif E H T.V T.cdvr T.t T.P W hW hWd h hi hl tW ⟨m⟩
  refine ⟨tW, m, PW, e, fun y => ?_⟩
  obtain ⟨u, n, hn, hc⟩ := T.mono (e y)
  have hn0 : T.be (e y) (e y) = 2 * (n 0 : ℤ) := hn 0
  obtain ⟨v, hv⟩ := he y _ hc
  refine ⟨by rw [hn0]; positivity, _, hv, ?_⟩
  have ht : (T.be (e y) (e y)).toNat = 2 * n 0 := by rw [hn0]; omega
  rw [ht]
  have hu : IsUnit ((v : W) * h u) := v.isUnit.mul (u.isUnit.map h)
  have e1 : ((v : W) * h (u * ∏ i, ![T.ϖ] i ^ n i)) ^ 2 = ((v : W) * h u) ^ 2 * h T.ϖ ^ (2 * n 0) := by
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow]
    ring
  rw [e1]
  exact associated_unit_mul_left _ _ (hu.pow 2)

end GlobalTheory.UPoinc.TraitPull
