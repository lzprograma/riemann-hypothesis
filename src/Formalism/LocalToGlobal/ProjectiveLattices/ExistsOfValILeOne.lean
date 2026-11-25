module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Matrix.PEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open Matrix IsDedekindDomain

variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]


theorem iwasawa : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 →
    ∃ (k : Matrix (Fin n) (Fin n) V) (U : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ U.BlockTriangular id ∧
      (∀ i, U i i ≠ 0) ∧ A = k.map (algebraMap V F) * U :=
  fun A hA => GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) A hA

theorem upper_inv {m : ℕ} (U : Matrix (Fin m) (Fin m) F) (hU : U.BlockTriangular id) (hd : ∀ i, U i i ≠ 0) :
    U⁻¹.BlockTriangular id ∧ (∀ i, U⁻¹ i i ≠ 0) ∧ U * U⁻¹ = 1 := by
  have hdet : U.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hU]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  have hu : IsUnit U.det := isUnit_iff_ne_zero.mpr hdet
  letI := Matrix.invertibleOfIsUnitDet U hu
  have hinv : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hU
  refine ⟨hinv, fun i => ?_, Matrix.mul_nonsing_inv U hu⟩
  have h1 : (U⁻¹ * U) i i = 1 := by rw [Matrix.nonsing_inv_mul U hu, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · rw [hinv hlt, zero_mul]
    · rw [hU hgt, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem iwasawa' {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) :
    ∃ (k : Matrix (Fin n) (Fin n) V) (N : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ N.BlockTriangular id ∧
      (∀ i, N i i ≠ 0) ∧ A * N = k.map (algebraMap V F) := by
  obtain ⟨k, U, hk, hU, hd, hA⟩ := iwasawa (V := V) A hA
  obtain ⟨hinv, hdinv, hUU⟩ := upper_inv U hU hd
  refine ⟨k, U⁻¹, hk, hinv, hdinv, ?_⟩
  rw [hA, Matrix.mul_assoc, hUU, Matrix.mul_one]

end Formalism.L2.Pj
