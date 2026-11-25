module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQkZeroOver
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem spMap_comp_tf {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V) {F₀ F : Type}
    [Field F₀] [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F] (j : F₀ →+* F) (hj : Ext f j) :
    spMap j ≫ (TF (R := R) F₀).hom = (TF (R := V) F).hom ≫ spMap f := by
  simp only [TF, jFK, jK, spMap, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact hj r

theorem tr_base {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {f : R →+* V} {D₀ : DegPre R}
    {D : DegPre V} {hD : IsPullDeg f D₀ D} {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F]
    [Algebra (FractionRing V) F] {j : F₀ →+* F} (hj : Ext f j) {g₀ : GtPtF D₀ F₀} {g : GtPtF D F}
    (h : Tr f hD j g₀ g) {X : Scheme.{0}} (m : D₀.P.A.left ⟶ X) (k : Sp R ⟶ X)
    (hg₀ : g₀.b.left ≫ m = (TF (R := R) F₀).hom ≫ k) :
    g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f)) ≫ m = (TF (R := V) F).hom ≫ spMap f ≫ k := by
  obtain ⟨g₁, ⟨hb, -⟩, hp⟩ := h
  rw [← Category.assoc, hp.1, hb, Category.assoc, hg₀, ← Category.assoc, spMap_comp_tf f j hj, Category.assoc]

end GlobalTheory.TInj
