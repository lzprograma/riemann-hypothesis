module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
open GlobalTheory.UT

namespace GlobalTheory

theorem splitTorus_hom_pullback_local_trivial {S : Scheme.{0}} (A : CommRingCat.{0}) [IsLocalRing A]
    [IsNoetherianRing A] (p : Spec A ⟶ S) (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (B : Over S) [GrpObj B] [IsProper B.hom] (f : splitTorus S X ⟶ B)
    (hf : IsMonHom f) :
    (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) := by
  obtain ⟨A⟩ := A
  refine TorusLocal.pullback_map_eq_one p X B f hf fun g hg ↦ ?_
  have : IsProper ((Over.pullback p).obj B).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  exact splitTorus_hom_proper_trivial_local A X _ g hg

theorem splitTorus_hom_abelian_eq_one : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over S) [GrpObj B], IsAbelianScheme B → ∀ f : splitTorus S X ⟶ B, IsMonHom f → f = 1 := by
  intro S _ X _ _ _ B _ hB f hf
  have := hB.proper
  refine Over.OverMorphism.ext (hom_ext_of_fromSpecStalk fun t ↦ ?_)
  let p := S.fromSpecStalk ((splitTorus S X).hom t)
  have h : (Over.pullback p).map f = (Over.pullback p).map (toUnit _ ≫ η[B]) :=
    splitTorus_hom_pullback_local_trivial _ p X B f hf
  have h₁ : ∀ u : splitTorus S X ⟶ B, ((Over.pullback p).map u).left ≫ pullback.fst B.hom p =
      pullback.fst (splitTorus S X).hom p ≫ u.left := fun u ↦ pullback.lift_fst _ _ _
  have h₂ : pullback.fst (splitTorus S X).hom p ≫ f.left =
      pullback.fst (splitTorus S X).hom p ≫ (1 : splitTorus S X ⟶ B).left := by
    rw [← h₁, ← h₁, h, Hom.one_def]
  have h₃ : pullback.lift ((splitTorus S X).left.fromSpecStalk t)
      (Spec.map ((splitTorus S X).hom.stalkMap t)) (Scheme.SpecMap_stalkMap_fromSpecStalk _).symm ≫
      pullback.fst (splitTorus S X).hom p = (splitTorus S X).left.fromSpecStalk t :=
    pullback.lift_fst _ _ _
  rw [← h₃, Category.assoc, Category.assoc, h₂]

end GlobalTheory
