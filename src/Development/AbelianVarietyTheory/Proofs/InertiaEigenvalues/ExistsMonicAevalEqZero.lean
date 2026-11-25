module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.Algebra.Spectrum.Basic

@[expose] public section

universe u_1

namespace GlobalTheory.IntegralTrace

open Polynomial

theorem exists_monic_aeval_eq_zero {R E : Type*} [CommRing R] [Field E] [Algebra R E] {n : ℕ}
    (L : Submodule R (Fin n → E)) (hL : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, M.mulVec x ∈ L) :
    ∃ p : R[X], p.Monic ∧ aeval M (p.map (algebraMap R E)) = 0 := by
  haveI : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  let g : Module.End R (Fin n → E) := (Matrix.toLin' M).restrictScalars R
  have hg : ∀ x ∈ L, g x ∈ L := fun x hx => by simpa [g] using hM x hx
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero R (g.restrict hg)
  refine ⟨p, hp, ?_⟩
  have key : ∀ (q : R[X]) (x : L), ((aeval (g.restrict hg) q x : L) : Fin n → E)
      = (aeval M (q.map (algebraMap R E))).mulVec x := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    | add a b ha hb =>
      intro x
      simp only [map_add (f := _), Polynomial.map_add (f := _), LinearMap.add_apply, Submodule.coe_add, ha, hb,
        Matrix.add_mulVec]
    | monomial k a ih =>
      intro x
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.map_mul, map_mul (aeval M), Module.End.mul_apply,
        ih,
        Polynomial.map_X, aeval_X, aeval_X, ← Matrix.mulVec_mulVec]
      rfl
  apply Matrix.toLin'.injective
  rw [map_zero]
  apply LinearMap.ext_on hspan
  intro x hx
  have := key p ⟨x, hx⟩
  rw [hp0] at this
  simpa using this.symm

/-- A matrix preserving a finitely generated submodule that spans the ambient space is integral. -/
theorem isIntegral_of_preserves_lattice {R E : Type*} [CommRing R] [Field E] [Algebra R E] {n : ℕ}
    (L : Submodule R (Fin n → E)) (hL : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (M : Matrix (Fin n) (Fin n) E) (hM : ∀ x ∈ L, M.mulVec x ∈ L) : IsIntegral R M := by
  obtain ⟨p, hp, h⟩ := exists_monic_aeval_eq_zero L hL hspan M hM
  exact ⟨p, hp, by rwa [aeval_map_algebraMap, aeval_def] at h⟩

/-- The trace of a matrix integral over the coefficient ring is integral over the same ring. -/
theorem isIntegral_trace_of_isIntegral {R K ι : Type*} [CommRing R] [Field K] [Algebra R K]
    [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K) (hM : IsIntegral R M) : IsIntegral R M.trace := by
  let L := AlgebraicClosure K
  let φ : Matrix ι ι K →ₐ[R] Matrix ι ι L := (IsScalarTower.toAlgHom R K L).mapMatrix
  obtain ⟨p, hp, hpM⟩ := hM.map φ
  have hN : aeval (φ M) (p.map (algebraMap R L)) = 0 := by
    rwa [aeval_map_algebraMap, aeval_def]
  have htr : algebraMap K L M.trace = (φ M).trace := AddMonoidHom.map_trace _ _
  rw [← isIntegral_algebraMap_iff (A := K) (B := L), htr, Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun z hz => ?_
  have hspec : z ∈ spectrum L (φ M) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (Polynomial.isRoot_of_mem_roots hz)
  have hz0 := spectrum.subset_polynomial_aeval (φ M) (p.map (algebraMap R L)) ⟨z, hspec, rfl⟩
  rw [hN, spectrum.mem_iff, sub_zero] at hz0
  have heval : eval z (p.map (algebraMap R L)) = 0 := by
    by_contra h
    exact hz0 ((IsUnit.mk0 _ h).map _)
  exact ⟨p, hp, by rwa [eval_map] at heval⟩

end GlobalTheory.IntegralTrace
