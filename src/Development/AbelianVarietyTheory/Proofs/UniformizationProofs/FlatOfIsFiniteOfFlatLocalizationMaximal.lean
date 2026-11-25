module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj

namespace GlobalTheory


open scoped TensorProduct in
theorem flat_SpecMap_of_flat_localization_maximal (V : Type) [CommRing V] (C : CommRingCat.{0})
    (f : CommRingCat.of V ⟶ C)
    (h : ∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd (Spec.map f)
      (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime m)))))) :
    Flat (Spec.map f) := by
  rw [Flat.SpecMap_iff]
  letI : Algebra V C := f.hom.toAlgebra
  have key : Module.Flat V C := by
    refine Module.flat_of_isLocalized_maximal V C (fun P _ => Localization.AtPrime P ⊗[V] C)
      (fun P _ => TensorProduct.mk V (Localization.AtPrime P) C 1) fun P _ => ?_
    have sq := (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct V (Localization.AtPrime P) C)).flip
    have h1 := h P
    have h2 := sq.isoPullback_hom_snd
    have h3 : Flat (sq.isoPullback.hom ≫ pullback.snd _ _) := by
      haveI : Flat (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap V C)))
        (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime P))))) := h1
      infer_instance
    rw [h2, Flat.SpecMap_iff] at h3
    haveI : Module.Flat (Localization.AtPrime P) (Localization.AtPrime P ⊗[V] C) :=
      RingHom.flat_algebraMap_iff.mp h3
    exact Module.Flat.trans V (Localization.AtPrime P) _
  exact key

theorem flat_of_isFinite_of_flat_localization_maximal :
    ∀ (V : Type) [CommRing V] (H : Over (Sp V)), IsFinite H.hom → (∀ (m : Ideal V) [m.IsMaximal], Flat (pullback.snd H.hom (spMap (algebraMap V (Localization.AtPrime m))))) → Flat H.hom := by
  intro V _ H hfin h
  haveI : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨f, hf⟩ := Spec.map_surjective (H.left.isoSpec.inv ≫ H.hom)
  have hf' : H.hom = H.left.isoSpec.hom ≫ Spec.map f := by rw [hf]; simp
  have : Flat (Spec.map f) := by
    refine flat_SpecMap_of_flat_localization_maximal V _ f fun m _ => ?_
    have h1 := h m
    rw [hf, ← pullbackRightPullbackFstIso_inv_snd_snd]
    haveI : Flat (pullback.snd H.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V (Localization.AtPrime m))))) := h1
    infer_instance
  rw [hf']
  infer_instance

end GlobalTheory
