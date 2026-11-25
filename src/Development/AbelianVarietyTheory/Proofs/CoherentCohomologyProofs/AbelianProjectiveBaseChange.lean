module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbProj

theorem isProjBy_of_isPullback {S : Scheme.{0}} (P : PolAV S) {R : Type} [CommRing R]
    {t : Spec (CommRingCat.of R) ⟶ S} {X : Scheme.{0}} {π : X ⟶ P.A.left}
    {f : X ⟶ Spec (CommRingCat.of R)} (h : IsPullback π f P.A.hom t) : IsProjBy f := by
  obtain ⟨N, -, m, s, hL, hs⟩ := polAV_veryAmpleBy
    (polBaseChange_of_relAmple_local AmpleLocal.relAmple_of_locally) S P R t X π f h
  exact ⟨_, hL, m, s, hs⟩

theorem abelian_projective_baseChange : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), (IsProjBy P.A.hom ∧ IsSeparated P.A.hom) ∧ ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ P.A.left) (Y : Scheme.{0}) (π : Y ⟶ (P.A ⊗ P.A).left) (f : Y ⟶ Spec (CommRingCat.of R)), IsPullback π f (fst P.A P.A).left t → IsProjBy f ∧ IsSeparated f ∧ Smooth f ∧ UniversallyClosed f ∧ Surjective f ∧ IsPullback (π ≫ (snd P.A P.A).left) f P.A.hom (t ≫ P.A.hom) := by
  intro K _ _ P
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have hsur : Surjective P.A.hom := inferInstance
  refine ⟨⟨isProjBy_of_isPullback P (IsPullback.id_horiz _), inferInstance⟩, ?_⟩
  intro R _ t Y π f h
  have h₀ : IsPullback (snd P.A P.A).left (fst P.A P.A).left P.A.hom P.A.hom :=
    (IsPullback.of_hasPullback P.A.hom P.A.hom).flip
  have h₁ : IsPullback (π ≫ (snd P.A P.A).left) f P.A.hom (t ≫ P.A.hom) := h.paste_horiz h₀
  exact ⟨isProjBy_of_isPullback P h₁,
    MorphismProperty.of_isPullback (P := @IsSeparated) h₁ inferInstance,
    MorphismProperty.of_isPullback (P := @Smooth) h₁ inferInstance,
    MorphismProperty.of_isPullback (P := @UniversallyClosed) h₁ inferInstance,
    MorphismProperty.of_isPullback (P := @Surjective) h₁ hsur, h₁⟩

end GlobalTheory.AbProj
