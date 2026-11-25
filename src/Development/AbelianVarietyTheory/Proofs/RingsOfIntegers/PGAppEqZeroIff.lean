module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZeroOfIsAffineOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.ExtDiv

theorem pG_app_eq_zero_iff {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (W : D.P.A.left.Opens) (f : Γ(D.P.A.left, W)) :
    (g.pG.left.app W).hom f = 0 ↔ ((fstG I e D.P.A).left.app W).hom f = 0 := by
  have := g.q_flat
  have := g.q_surj

  have hpG : g.pG.left = g.q.left ≫ (fstG I e D.P.A).left := rfl
  have gen : ∀ φ : (thickObj R I e G).left ⟶ D.P.A.left, φ = g.q.left ≫ (fstG I e D.P.A).left →
      ((φ.app W).hom f = 0 ↔ ((fstG I e D.P.A).left.app W).hom f = 0) := by
    rintro φ rfl
    change (g.q.left.app ((fstG I e D.P.A).left ⁻¹ᵁ W)).hom
      (((fstG I e D.P.A).left.app W).hom f) = 0 ↔ _
    constructor
    · intro h

      apply GlobalTheory.FunDescent.app_injective g.q.left
      rw [h, map_zero]
    · intro h
      rw [h, map_zero]
  exact gen _ hpG

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G) (e k : ℕ) (α : D.toPre.X) (f : D.toPre.SecB k α), (∀ j, ((U.gt e).pG.left.app _).hom (f.f j) = 0) ↔ ∃ g : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom (ϖ ^ (e + 1)) f g := by
  intro V _ _ _ ϖ hϖ D A G _ _ U e k α f

  have hflat : Flat D.toPre.P.A.hom := by
    have := D.toPre.P.smoothDim.smooth
    infer_instance

  have hiff : (∀ j, ((U.gt e).pG.left.app _).hom (f.f j) = 0) ↔
      ∀ j, ((fstG (maximalIdeal V) e D.toPre.P.A).left.app _).hom (f.f j) = 0 :=
    forall_congr' fun j => pG_app_eq_zero_iff (U.gt e) _ (f.f j)
  rw [hiff]
  exact GlobalTheory.ThickDiv.main V ϖ hϖ D.toPre.P.A _ f e

end GlobalTheory.ExtDiv
