module

public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobFnsDvrPf
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
open GlobalTheory.ChartCmp

namespace GlobalTheory.ModelSquareFunctions

theorem isProper_genericFibre {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr}
    {y : letI := io.toAlgebra; FrPt Xo c T.Fr} (I : IntData Xo c T io y) :
    IsProper ((Over.pullback (spMap (algebraMap T.V (FractionRing T.V)))).obj I.G.G).hom := by
  have h1 := I.m1.cart.1
  have h2 := I.m2.cart.1
  have hp : IsProper I.t'.G.hom := MorphismProperty.of_isPullback h1 Xo.univ.proper
  show IsProper (pullback.snd I.G.G.hom (spMap (algebraMap T.V (FractionRing T.V))))
  rw [← h2.isoPullback_inv_snd]
  infer_instance

theorem surjective_appTop_square : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y), Function.Surjective (I.G.G ⊗ I.G.G).hom.appTop.hom := by
  intro E _ _ _ H Dw l Xo c T io y I
  have h := (globalFnsDvr_of_globalFns GlobalTheory.globalFns_holds E H T.V T.cpl I.G (isProper_genericFibre I) 2).2
  let e : powObj I.G.G 2 ≅ I.G.G ⊗ I.G.G := I.G.G ◁ᵢ (ρ_ I.G.G)
  have hw : e.inv.left ≫ (powObj I.G.G 2).hom = (I.G.G ⊗ I.G.G).hom := Over.w e.inv
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have : IsIso e.inv.left.appTop := inferInstanceAs (IsIso (e.inv.left.app ⊤))
  rw [← hw, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso e.inv.left.appTop).2.comp h

end GlobalTheory.ModelSquareFunctions
