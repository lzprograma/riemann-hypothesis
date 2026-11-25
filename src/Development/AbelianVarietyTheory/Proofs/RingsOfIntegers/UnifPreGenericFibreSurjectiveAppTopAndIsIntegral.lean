module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isIntegral_left_of_isAbelianScheme_field {K : Type} [Field K]
    (A : Over (Spec (CommRingCat.of K))) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left := by
  obtain ⟨-, hs, -, hc⟩ := hA
  have : ConnectedSpace A.left := GeometricallyConnected.connectedSpace_of_subsingleton (f := A.hom)
  exact isIntegral_of_smooth_field_of_connectedSpace A.hom

theorem unifPre_genericFibre_surjective_appTop_and_isIntegral :
    GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), Function.Surjective (pullback.snd G.hom (jK R)).appTop.hom ∧ IsIntegral (pullback G.hom (jK R)) := by
  intro hGF R _ _ I D A G _ _ U
  have hAi : IsIntegral A.A.left := isIntegral_left_of_isAbelianScheme_field A.A A.isAb
  have hw : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
  have : IsIso U.gen.hom.left := (Over.forget _).map_isIso U.gen.hom
  refine ⟨?_, ?_⟩
  · have hb := hGF _ A.A A.isAb
    rw [← hw, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    have : IsIso U.gen.hom.left.appTop := inferInstanceAs (IsIso (U.gen.hom.left.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso (U.gen.hom.left.appTop)).surjective.comp hb.surjective
  · show IsIntegral ((Over.pullback (jK R)).obj G).left
    have : Nonempty ((Over.pullback (jK R)).obj G).left :=
      ⟨U.gen.inv.left (Classical.arbitrary A.A.left)⟩
    exact isIntegral_of_isOpenImmersion U.gen.hom.left

end GlobalTheory
