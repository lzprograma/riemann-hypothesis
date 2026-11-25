module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingExistsAevalOfCommuteSeparable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AevalRootEqZeroIff
public import Formalism.SatakeDualWeyl.StatementF
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorSemilocalOfCyclicVectorField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.UsideLeaf.UnitaryLocalCharpoly

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

instance isLocalRing_intL : IsLocalRing (intL L) :=
  inferInstanceAs (IsLocalRing (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring)

theorem isCsr_charpoly {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (M J Ji : Matrix (Fin n) (Fin n) R)
    (hJ : Ji * J = 1) (hM : cT s M * J * M = J) : GlobalTheory.UTr.IsCsr s M.charpoly := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hJ' : J * Ji = 1 := mul_eq_one_comm.1 hJ
  let u : (Matrix (Fin n) (Fin n) R)ˣ := ⟨Ji, J, hJ, hJ'⟩
  set N := Ji * cT s M * J with hNdef
  have hNM : N * M = 1 := by
    rw [hNdef, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s M), hM, hJ]
  have hdeg : M.charpoly.natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hdegN : N.charpoly.natDegree = n := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hNc : N.charpoly = (cT s M).charpoly := by
    have := Matrix.charpoly_units_conj u (cT s M)
    rw [← Matrix.coe_units_inv] at this
    exact this
  have hmap : M.charpoly.map s = N.charpoly := by
    rw [hNc, ← Matrix.charpoly_map, ← Matrix.charpoly_transpose]; rfl
  have hrev : (M.charpoly.map s).reflect n = N.charpolyRev := by
    rw [hmap, ← Matrix.reverse_charpoly, Polynomial.reverse, hdegN]
  have hdetN : N.det * M.det = 1 := by rw [← Matrix.det_mul, hNM, Matrix.det_one]
  have hNd : N.det = s M.det := by
    have h1 : N.det = (cT s M).det := by
      rw [hNdef, Matrix.det_mul, Matrix.det_mul, mul_comm (Ji.det), mul_assoc, ← Matrix.det_mul, hJ,
        Matrix.det_one, mul_one]
    rw [h1, cT, Matrix.det_transpose, RingHom.map_det]; rfl
  have h0 : M.charpoly.coeff 0 = (-1) ^ n * M.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
      one_pow, one_mul]
  have hs0 : s (M.charpoly.coeff 0) = (-1) ^ n * N.det := by
    rw [h0, map_mul, map_pow, map_neg, map_one, hNd]
  refine ⟨Matrix.charpoly_monic M, ?_⟩
  rw [hdeg, hrev, Matrix.charpolyRev, hs0]
  have hA : (1 - (X : R[X]) • N.map C) * M.map C = -charmatrix M := by
    rw [sub_mul, one_mul, smul_mul_assoc, ← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero C) (map_one C),
      charmatrix, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply, neg_sub]; rfl
  have e1 : (1 - (X : R[X]) • N.map C).det * C M.det = (-1) ^ n * M.charpoly := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.det_mul, hA, Matrix.det_neg, Fintype.card_fin]; rfl
  have e2 : C N.det * C M.det = (1 : R[X]) := by rw [← C_mul, hdetN, C_1]
  rw [C_mul, C_pow, C_neg, C_1]
  linear_combination (-C N.det) * e1 + (1 - (X : R[X]) • N.map C).det * e2

theorem exists_poly_of_commute {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (M x : Matrix (Fin n) (Fin n) O)
    (hs : M.charpoly.Separable) (hc : x * M = M * x) : ∃ p : O[X], x = aeval M p := by
  apply GlobalTheory.LocalCommutant.exists_aeval_of_comm <;> assumption

end GlobalTheory.UsideLeaf.UnitaryLocalCharpoly
