module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRigidifiedExtensionOfGenericFibre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing

namespace GlobalTheory

theorem exists_lineBundle_extension_of_genericFibre_dvr :
    ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ N : LB (pullback G.hom (spMap (algebraMap W K'))), N.IsLB → ∃ (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), M.IsLB ∧ w.IsGen := by
  intro R K _ _ _ _ _ _ A _ hA N hN
  have hφ := IsPullback.of_hasPullback A.hom (spMap (algebraMap R K))
  have := hA.smooth
  have := hA.proper
  have hR : IsRegularRing R := inferInstance
  have : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth
      hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : GeometricallyIntegral (pullback.snd A.hom (spMap (algebraMap R K))) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) hφ inferInstance
  have : Smooth (pullback.snd A.hom (spMap (algebraMap R K))) :=
    MorphismProperty.of_isPullback (P := @Smooth) hφ inferInstance
  have : IsIntegral (pullback A.hom (spMap (algebraMap R K))) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
      (pullback.snd A.hom (spMap (algebraMap R K)))
  have h1 : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h2 : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors R))
  have : IsPreimmersion (pullback.fst A.hom (spMap (algebraMap R K))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hφ.flip h1
  have : Flat (pullback.fst A.hom (spMap (algebraMap R K))) :=
    MorphismProperty.of_isPullback (P := @Flat) hφ.flip h2
  have hst : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth R A.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  obtain ⟨L, hL, w, hw⟩ := exists_lineBundle_extension_of_generalizing A.left _
    (pullback.fst A.hom (spMap (algebraMap R K))) (Flat.generalizingMap _) hst N hN
  exact ⟨L, w, hL, hw⟩

end GlobalTheory
