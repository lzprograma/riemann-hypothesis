module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueComapEqVanishingIdeal
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ProjSpace

theorem baseChange_appLE_chartAlgEquiv {R R' : Type} [CommRing R] [CommRing R'] (N : ℕ) (φ : R →+* R')
    (i : Fin (N + 1)) (q : MvPolynomial {j // j ≠ i} R) :
    ((baseChange N φ).appLE (chart R N i) (chart R' N i) (baseChange_preimage_chart N φ i).ge).hom
      (chartAlgEquiv R N i q) = chartAlgEquiv R' N i (MvPolynomial.map φ q) := by
  have h : ((baseChange N φ).appLE (chart R N i) (chart R' N i)
      (baseChange_preimage_chart N φ i).ge).hom.comp (RingHomClass.toRingHom (chartAlgEquiv R N i)) =
      (RingHomClass.toRingHom (chartAlgEquiv R' N i)).comp (MvPolynomial.map φ) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.map_C]
      have h1 : chartAlgEquiv R N i (MvPolynomial.C r) = _ := (chartAlgEquiv R N i).commutes r
      have h2 : chartAlgEquiv R' N i (MvPolynomial.C (φ r)) = _ := (chartAlgEquiv R' N i).commutes (φ r)
      rw [h1, h2, ← formOn_C (i := i) (hi := le_rfl), ← formOn_C (i := i) (hi := le_rfl)]
      have h3 := baseChange_app_formOn φ (le_refl (chart R N i)) (MvPolynomial.isHomogeneous_C _ r)
      refine (congrArg (resG _ (baseChange_preimage_chart N φ i).ge) h3).trans ?_
      rw [resG_formOn]
      congr 1
      exact MvPolynomial.map_C _ _
    · simp only [RingHom.comp_apply, RingHom.coe_coe, MvPolynomial.map_X, chartAlgEquiv_X]
      have h3 := baseChange_app_ratioOn φ (le_refl (chart R N i)) j.1
      exact congrArg (resG _ (baseChange_preimage_chart N φ i).ge) h3
  exact congrArg (fun ψ => ψ q) h


theorem comap_map_baseChange {R R' : Type} [CommRing R] [CommRing R'] (N : ℕ) (φ : R →+* R')
    (I : (PSpace R' N).IdealSheafData) (T : ∀ i : Fin (N + 1), Set (MvPolynomial {j // j ≠ i} R'))
    (hT : ∀ i, Ideal.span (chartAlgEquiv R' N i '' T i) = I.ideal ⟨_, isAffineOpen_chart R' N i⟩)
    (hφ : ∀ i, T i ⊆ Set.range (MvPolynomial.map φ)) :
    (I.map (baseChange N φ)).comap (baseChange N φ) = I := by
  have : IsAffineHom (baseChange N φ) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_baseChange N φ).flip inferInstance
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun i => ⟨_, isAffineOpen_chart R' N i⟩) (iSup_chart R' N) fun i => ?_
  rw [← hT, Ideal.span_le]
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨q, rfl⟩ := hφ i ht
  have h0 : chartAlgEquiv R' N i (MvPolynomial.map φ q) ∈ I.ideal ⟨_, isAffineOpen_chart R' N i⟩ := by
    rw [← hT]
    exact Ideal.subset_span ⟨_, ht, rfl⟩
  rw [← baseChange_appLE_chartAlgEquiv] at h0 ⊢
  refine GlobalTheory.GaloisDescent.ideal_le_comap_appLE (baseChange N φ) le_rfl ⟨_, isAffineOpen_chart R N i⟩
    ⟨_, isAffineOpen_chart R' N i⟩ (baseChange_preimage_chart N φ i).ge ?_
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom, Ideal.mem_comap]
  have h1 := I.ideal_le_comap_ideal
    (U := ⟨_, (isAffineOpen_chart R N i).preimage (baseChange N φ)⟩)
    (V := ⟨_, isAffineOpen_chart R' N i⟩) (baseChange_preimage_chart N φ i).le h0
  rw [Ideal.mem_comap, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map] at h1
  rw [Scheme.Hom.app_eq_appLE]
  exact h1

end GlobalTheory.ProjSpace

namespace GlobalTheory


open ProjSpace in
theorem exists_finset_isProjOver_descends : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∃ s : Finset K, ∀ K₁ : Subfield K, K₀ ≤ K₁ → (s : Set K) ⊆ K₁ → ∃ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ : X ⟶ X₁), IsProjOver p₁ ∧ IsPullback φ p p₁ (spMap K₁.subtype) := by
  classical
  rintro K _ K₀ X p ⟨N, e, he, rfl⟩
  have hT : ∀ i : Fin (N + 1), ∃ T : Finset (MvPolynomial {j // j ≠ i} K),
      Ideal.span (chartAlgEquiv K N i '' T) = e.ker.ideal ⟨_, isAffineOpen_chart K N i⟩ := fun i => by
    obtain ⟨T, hT⟩ := (IsNoetherian.noetherian
      ((e.ker.ideal ⟨_, isAffineOpen_chart K N i⟩).comap (chartAlgEquiv K N i)))
    refine ⟨T, ?_⟩
    have := congrArg (Ideal.map (chartAlgEquiv K N i)) hT
    rw [Ideal.map_comap_of_surjective _ (chartAlgEquiv K N i).surjective] at this
    rw [← this]
    exact (Ideal.map_span _ _).symm
  choose T hT using hT
  refine ⟨Finset.univ.biUnion fun i => (T i).biUnion MvPolynomial.coeffs, fun K₁ _ hs => ?_⟩
  have key := comap_map_baseChange N K₁.subtype e.ker (fun i => T i) hT fun i t ht => by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.2
    intro c hc
    refine ⟨⟨c, hs ?_⟩, rfl⟩
    simp only [Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨i, Finset.mem_univ i, t, ht, hc⟩
  rw [Scheme.IdealSheafData.map_ker] at key
  refine ⟨(e ≫ baseChange N K₁.subtype).image, (e ≫ baseChange N K₁.subtype).imageι ≫ PSpace.str K₁ N,
    (e ≫ baseChange N K₁.subtype).toImage, ⟨N, _, inferInstance, rfl⟩, ?_⟩
  have h := isPullback_of_isClosedImmersion e (e ≫ baseChange N K₁.subtype).imageι
    (e ≫ baseChange N K₁.subtype).toImage (baseChange N K₁.subtype) (by simp)
    (by rw [← key]; congr 1; exact Scheme.IdealSheafData.ker_subschemeι _)
  exact h.flip.paste_vert (isPullback_baseChange N K₁.subtype)

end GlobalTheory
