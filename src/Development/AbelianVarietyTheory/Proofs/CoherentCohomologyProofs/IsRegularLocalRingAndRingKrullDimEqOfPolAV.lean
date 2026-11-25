module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
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
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem isRegularLocalRing_and_ringKrullDim_eq_of_polAV :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t₀ : Spec (CommRingCat.of R) ⟶ P.A.left) (m : Ideal R) [m.IsMaximal] (O : Type) [CommRing O] [Algebra R O] [IsLocalization.AtPrime O m], IsOpenImmersion t₀ → IsRegularLocalRing O ∧ ringKrullDim O = P.g := by
  intro K _ _ P R _ t₀ m hm O _ _ _ ht
  have hab := P.isAb
  have hd := P.smoothDim
  have hsm : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  have hgi : GeometricallyIntegral P.A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hsm hab.geomConnected
  have hint : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  have hnt : Nontrivial R := ⟨⟨0, 1, fun h => hm.ne_top ((Ideal.eq_top_iff_one m).2 (h ▸ m.zero_mem))⟩⟩
  let φ : CommRingCat.of K ⟶ CommRingCat.of R := Spec.preimage (t₀ ≫ P.A.hom)
  have hφ : t₀ ≫ P.A.hom = Spec.map φ := (Spec.map_preimage _).symm
  let _ : Algebra K R := φ.hom.toAlgebra
  have hφ' : t₀ ≫ P.A.hom = Spec.map (CommRingCat.ofHom (algebraMap K R)) := hφ
  have htr : Algebra.trdeg K R = P.g :=
    trdeg_eq_of_smoothOfRelativeDimension K P.A.left P.A.hom P.g hd R t₀ ht hφ'
  have : IsIntegral (Spec (CommRingCat.of R)) := isIntegral_of_isOpenImmersion t₀
  have : IsDomain R := (affine_isIntegral_iff (CommRingCat.of R)).1 inferInstance
  have hs : Smooth (Spec.map φ) := hφ ▸ inferInstance
  have hs' : Algebra.Smooth K R := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hs
  have hreg : IsRegularRing R := isRegularRing_of_smooth K R
  have hh := ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field P.g htr m
  refine ⟨?_, ?_⟩
  · have := isRegularRing_iff.mp hreg m
    exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv m.primeCompl
      (Localization.AtPrime m) O).toRingEquiv
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height m O, hh]
    rfl

end GlobalTheory
