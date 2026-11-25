module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Mathlib.RingTheory.Flat.TorsionFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SmoothStalkNormal

theorem flat_fromSpecStalk' (X : Scheme.{0}) (x : X) : Flat (X.fromSpecStalk x) := by
  exact GlobalTheory.Reg.ChartGenerator.flat_fromSpecStalk x

theorem injective_of_flat_of_isDomain {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Nontrivial B] (f : A →+* B) (hf : f.Flat) : Function.Injective f := by
  algebraize [f]
  refine (injective_iff_map_eq_zero f).2 fun r hr => ?_
  by_contra h0
  have hreg : IsSMulRegular B r :=
    Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero h0)
  have h1 : r • (1 : B) = r • (0 : B) := by
    rw [smul_zero, Algebra.smul_def, _root_.mul_one]; exact hr
  exact one_ne_zero (hreg h1)

theorem stalk_of_smooth_over_regular :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (X : Scheme.{0}) (p : X ⟶ Sp R), Smooth p →
      ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) ∧
        IsIntegrallyClosed (X.presheaf.stalk x) ∧
        (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat ∧
        Function.Injective (Spec.preimage (X.fromSpecStalk x ≫ p)).hom := by
  intro R _ _ X p hp x
  haveI : Smooth p := hp
  haveI : IsRegularRing (CommRingCat.of R) := GlobalTheory.isRegularRing_of_isRegularLocalRing R
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth p x
  obtain ⟨hdom, hint⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (X.presheaf.stalk x)
  have hRdom : IsDomain R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).1
  have hfl : (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat := by
    haveI := flat_fromSpecStalk' X x
    have h : Flat (Spec.map (Spec.preimage (X.fromSpecStalk x ≫ p))) := by
      rw [Spec.map_preimage]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 h
  refine ⟨hdom, inferInstance, hint, hfl, ?_⟩
  exact injective_of_flat_of_isDomain (A := R) _ hfl

end GlobalTheory.SmoothStalkNormal
