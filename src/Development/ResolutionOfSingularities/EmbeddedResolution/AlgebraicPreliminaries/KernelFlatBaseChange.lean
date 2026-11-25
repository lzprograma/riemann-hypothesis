module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace FunctorialResolution.EmbeddedResolution

private theorem lid_rTensor_subtype_mem_map {R A' : Type*} [CommRing R] [CommRing A'] [Algebra R A']
    (K : Ideal R) (y : K ⊗[R] A') :
    (TensorProduct.lid R A') (LinearMap.rTensor A' K.subtype y) ∈ K.map (algebraMap R A') := by
  induction y using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero]
      exact Submodule.zero_mem _
  | tmul k a =>
      have hka : (TensorProduct.lid R A') (LinearMap.rTensor A' K.subtype (k ⊗ₜ[R] a))
          = (k : R) • a := by simp
      rw [hka, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ k.2)
  | add y z hy hz =>
      rw [map_add (f := _), map_add (f := _)]
      exact Submodule.add_mem _ hy hz

private theorem algebraMap_tmul_one_eq_one_tmul_algebraMap {A B A' : Type*} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] (a : A) :
    (algebraMap A B a) ⊗ₜ[A] (1 : A') = (1 : B) ⊗ₜ[A] (algebraMap A A' a) := by
  calc (algebraMap A B a) ⊗ₜ[A] (1 : A') = (a • (1 : B)) ⊗ₜ[A] (1 : A') := by
        rw [Algebra.algebraMap_eq_smul_one]
    _ = a • ((1 : B) ⊗ₜ[A] (1 : A')) := TensorProduct.smul_tmul' a (1 : B) (1 : A')
    _ = (1 : B) ⊗ₜ[A] (a • (1 : A')) := (TensorProduct.tmul_smul a (1 : B) (1 : A')).symm
    _ = (1 : B) ⊗ₜ[A] (algebraMap A A' a) := by rw [Algebra.algebraMap_eq_smul_one]

theorem ker_includeRight_eq_map_ker (R B A' : Type*) [CommRing R] [CommRing B] [CommRing A']
    [Algebra R B] [Algebra R A'] [Module.Flat R A'] :
    RingHom.ker (Algebra.TensorProduct.includeRight : A' →ₐ[R] B ⊗[R] A').toRingHom =
      (RingHom.ker (algebraMap R B)).map (algebraMap R A') := by
  have hex : Function.Exact ((RingHom.ker (algebraMap R B)).subtype) (Algebra.linearMap R B) := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    ext r
    simp [RingHom.mem_ker]
  have hflat : Function.Exact
      (LinearMap.rTensor A' ((RingHom.ker (algebraMap R B)).subtype))
      (LinearMap.rTensor A' (Algebra.linearMap R B)) :=
    Module.Flat.rTensor_exact (R := R) (M := A') hex
  apply le_antisymm
  · intro x hx
    have hx0 : (1 : B) ⊗ₜ[R] x = 0 := by
      simpa [RingHom.mem_ker, Algebra.TensorProduct.includeRight_apply,
        AlgHom.toRingHom_eq_coe] using hx
    have key : (LinearMap.rTensor A' (Algebra.linearMap R B)) ((1 : R) ⊗ₜ[R] x) = 0 := by
      simpa using hx0
    have hmem : (1 : R) ⊗ₜ[R] x ∈
        LinearMap.range (LinearMap.rTensor A' ((RingHom.ker (algebraMap R B)).subtype)) := by
      rw [← LinearMap.exact_iff.mp hflat]
      exact LinearMap.mem_ker.mpr key
    obtain ⟨y, hy⟩ := hmem
    have hx1 : x = (TensorProduct.lid R A') ((1 : R) ⊗ₜ[R] x) := by simp
    rw [hx1, ← hy]
    exact lid_rTensor_subtype_mem_map _ y
  · rw [Ideal.map_le_iff_le_comap]
    intro k hk
    have hk0 : algebraMap R B k = 0 := RingHom.mem_ker.mp hk
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e1 : (Algebra.TensorProduct.includeRight : A' →ₐ[R] B ⊗[R] A')
        (algebraMap R A' k) = 0 := by
      rw [Algebra.TensorProduct.includeRight_apply, ← algebraMap_tmul_one_eq_one_tmul_algebraMap, hk0,
        TensorProduct.zero_tmul]
    exact e1

theorem quasiCompact_of_isPullback {Z X X' Z' : Scheme.{u}} {h : Z ⟶ X} {g : X' ⟶ X}
    {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g) [QuasiCompact h] :
    QuasiCompact h' :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) H ‹QuasiCompact h›

theorem ker_eq_comap_ker_of_isPullback_of_flat {Z X X' Z' : Scheme.{u}} {h : Z ⟶ X} {g : X' ⟶ X}
    {g' : Z' ⟶ Z} {h' : Z' ⟶ X'} (H : IsPullback g' h' h g)
    [QuasiCompact h] [QuasiCompact h'] [AlgebraicGeometry.Flat g] :
    h'.ker = h.ker.comap g :=
  GlobalTheory.ker_eq_comap_of_flat h H.flip

end FunctorialResolution.EmbeddedResolution
