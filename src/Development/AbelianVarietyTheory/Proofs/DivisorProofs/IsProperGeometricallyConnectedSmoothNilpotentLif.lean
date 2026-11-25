module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndGeometricallyConnectedOfIsNilpotent
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.RingTheory.DividedPowers.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

namespace GlobalTheory.NilLift

theorem surjective_spMap_of_isNilpotent_ker {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π)) : Surjective (spMap π) := by
  refine ⟨fun (x : PrimeSpectrum R) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    obtain ⟨n, hn⟩ := hn
    intro a ha
    apply x.isPrime.mem_of_pow_mem n
    have : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    rw [show a ^ n = 0 from this]
    exact zero_mem _
  exact this

theorem isProper_and_geometricallyConnected_of_smooth_lift :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    IsProper X₀.hom → GeometricallyConnected X₀.hom → IsProper X.hom ∧ GeometricallyConnected X.hom := by
  intro R R₀ _ _ π hπ hn X X₀ i hsq hsm hp hgc
  have hs : Surjective (spMap π) := surjective_spMap_of_isNilpotent_ker π hπ hn
  have hc : IsClosedImmersion (spMap π) := .spec_of_surjective _ hπ
  have : Surjective i := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hs
  have : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hc
  have : IsProper (i ≫ X.hom) := by rw [hsq.w]; infer_instance
  have : UniversallyClosed X.hom := UniversallyClosed.of_comp_surjective i X.hom
  have : IsSeparated X.hom := GlobalTheory.NilProper.isSeparated_of_comp_surjective i X.hom
  have : LocallyOfFiniteType X.hom := inferInstance
  refine ⟨{}, ⟨fun K _ y Z fst snd hz ↦ ?_⟩⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective y
  have hφ : RingHom.ker π ≤ RingHom.ker φ.hom := by
    intro a ha
    obtain ⟨n, hn⟩ := hn
    have : a ^ n ∈ RingHom.ker π ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    have h0 : IsNilpotent a := ⟨n, this⟩
    exact (h0.map φ.hom).eq_zero
  let ψ : R₀ →+* K := RingHom.liftOfSurjective π hπ ⟨φ.hom, hφ⟩
  have hψ : ∀ a, ψ (π a) = φ.hom a := fun a ↦
    RingHom.liftOfRightInverse_comp_apply π _ _ ⟨φ.hom, hφ⟩ a
  let y' : Spec (CommRingCat.of K) ⟶ Sp R₀ := Spec.map (CommRingCat.ofHom ψ)
  have hy : y' ≫ spMap π = Spec.map φ := by
    simp only [y', spMap, ← Spec.map_comp]
    congr 1
    ext a
    exact hψ a
  rw [← hy] at hz
  let p : Z ⟶ X₀.left := hsq.lift fst (snd ≫ y') (by rw [hz.w, Category.assoc])
  refine hgc.geometrically_connectedSpace y' p snd ?_
  exact IsPullback.of_right (by rw [hsq.lift_fst]; exact hz) (hsq.lift_snd _ _ _) hsq

end GlobalTheory.NilLift
