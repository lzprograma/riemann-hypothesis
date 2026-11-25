module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
public import Formalism.HermitianCurvature.StatementG

@[expose] public section

open Matrix
open Formalism.FourierDecayAlt.G

namespace Formalism.FourierDecayAlt.P.G4

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := Formalism.FourierDecayAlt.P.G2.blk_cc A b a e i j

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  apply _root_.Formalism.FourierDecayAlt.P.G2.blk_cl <;> assumption

theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  apply _root_.Formalism.FourierDecayAlt.P.G2.blk_lc <;> assumption

theorem blk_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b a b' a' : Fin n → ℂ) (e e' : ℂ) :
    blk A b a e * blk A' b' a' e' =
      blk (A * A' + Matrix.vecMulVec b a') (A *ᵥ b' + e' • b) (a ᵥ* A' + e • a') (a ⬝ᵥ b' + e * e') := by
  apply _root_.Formalism.FourierDecayAlt.P.G2.blk_mul <;> assumption

theorem upperUni_det {d : ℕ} {u : Matrix (Fin d) (Fin d) ℂ} (hu : IsUpperUni u) : u.det = 1 := by
  have h : u.BlockTriangular id := fun i j hij => hu.2 i j hij
  rw [Matrix.det_of_isUpperTriangular h]
  simp [hu.1]

theorem superSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    superSum (blk A b a e) = superSum A + b (Fin.last m) := by
  unfold superSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_cl]

theorem subSum_blk {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (b a : Fin (m + 1) → ℂ) (e : ℂ) :
    subSum (blk A b a e) = subSum A + a (Fin.last m) := by
  unfold subSum
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, blk_cc]
  · rw [Fin.succ_last, blk_lc]

end Formalism.FourierDecayAlt.P.G4
