module

import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosureProperties
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Mathlib.Algebra.Order.Archimedean.Real.Hom

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

theorem theta_real : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → (∃ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ) ∧ ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ → ∀ (t : ℝ) (w : InfinitePlace F), ‖θ t w‖ = |t| := by
  intro F _ _ hF
  have hw : ∀ w : InfinitePlace F, w.IsReal := hF.isReal
  refine ⟨⟨Pi.ringHom fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (hw w)).symm.toRingHom,
    continuous_pi fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (hw w)).symm.continuous⟩,
    fun θ _ t w => ?_⟩
  have h1 : ((InfinitePlace.Completion.ringEquivRealOfIsReal (hw w)).toRingHom.comp
      ((Pi.evalRingHom _ w).comp θ)) = RingHom.id ℝ := Subsingleton.elim _ _
  have h2 : InfinitePlace.Completion.extensionEmbeddingOfIsReal (hw w) (θ t w) = t := DFunLike.congr_fun h1 t
  rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hw w)).norm_map_of_map_zero (map_zero _), h2,
    Real.norm_eq_abs]

theorem up_fin {F : Type} [Field F] [NumberField F] {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0} :
    IsUnitProd a c ↔ ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → (∀ v, v ∉ S → c v = 1) ∧ a * ∏ v ∈ S, c v = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    have hf := Filter.eventually_cofinite.1 h1
    refine ⟨hf.toFinset, fun S hS => ⟨fun v hv => by_contra fun h => hv (hS (hf.mem_toFinset.2 h)), ?_⟩⟩
    rw [← finprod_eq_prod_of_mulSupport_subset c fun v hv => hS (hf.mem_toFinset.2 hv), h2]
  · rintro ⟨S, h⟩
    obtain ⟨h1, h2⟩ := h S le_rfl
    exact ⟨S.eventually_cofinite_notMem.mono h1, by
      rw [finprod_eq_prod_of_mulSupport_subset c fun v hv => by_contra fun h => hv (h1 v h), h2]⟩

theorem up_alg : ∀ (F : Type) [Field F] [NumberField F] (a b : ℝ≥0) (c e : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd a c → IsUnitProd b e → a ≠ 0 ∧ (∀ v, c v ≠ 0) ∧ IsUnitProd (a * b) (fun v => c v * e v) ∧ IsUnitProd a⁻¹ (fun v => (c v)⁻¹) ∧ IsUnitProd (a / b) (fun v => c v / e v) ∧ IsUnitProd (NNReal.sqrt a) (fun v => NNReal.sqrt (c v)) ∧ (∀ n : ℕ, IsUnitProd (a ^ n) (fun v => c v ^ n)) ∧ ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → (∀ v, v ∉ S → c v = 1) ∧ a * ∏ v ∈ S, c v = 1 := by
  apply GlobalTheory.CompanionTheory.SW.UnitProdAlg.main

end PositivityTheory.PlacePermOperatorBicommutantSpan
