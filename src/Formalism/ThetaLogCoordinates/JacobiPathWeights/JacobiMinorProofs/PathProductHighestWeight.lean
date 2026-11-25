module

import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.JacobiMinorProof
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementA
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementC
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ActFormContract
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace A1hw

theorem mem_can {n : ℕ} {μN : Fin n → ℤ} (h : Antitone μN) (c : ℤ) (m : Fin n) :
    m ∈ canIdx μN c ↔ if 1 ≤ c then c ≤ μN m else μN m < c := by
  unfold canIdx
  split_ifs with hc
  · simp only [mem_filter, mem_univ, true_and]
    exact (Paths.le_iff_lt_colHeight h c m).symm
  · simp only [mem_filter, mem_univ, true_and]
    rw [← not_le, Paths.le_iff_lt_colHeight h c m, not_lt]

theorem isIndex_can {n : ℕ} (μN : Fin n → ℤ) : IsIndex μN (canIdx μN) := by
  apply Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.canIdx_isIndex

theorem map_step {A A' : Type*} [CommRing A] [CommRing A'] (φ : A →+* A') {n : ℕ} (up : Bool)
    (K : Form A n) (K' : Form A' n) (Xv : Fin n → A) (hK : ∀ J, φ (K J) = K' J) (J : Finset (Fin n)) :
    φ (stepF up K Xv J) = stepF up K' (fun a => φ (Xv a)) J := by
  unfold stepF
  cases up

  · simp only [Bool.false_eq_true, ite_false, contrF, map_sum, map_mul, map_intCast, hK]

  · simp only [ite_true, wedgeF, map_sum, map_mul, map_intCast, hK]

theorem map_pathWord {A A' : Type*} [CommRing A] [CommRing A'] (φ : A →+* A') {n : ℕ}
    (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ) (Xr : ℕ → Fin n → A) :
    ∀ (j : ℕ) (J : Finset (Fin n)),
      φ (pathWord isVec μ c Xr j J) = pathWord isVec μ c (fun i a => φ (Xr i a)) j J := by
  intro j
  induction j with
  | zero =>
    intro J
    show φ (if J = ∅ then 1 else 0) = if J = ∅ then 1 else 0
    split <;> simp
  | succ j ih =>
    intro J
    by_cases hch : colHeight (μ (j + 1)) c = colHeight (μ j) c
    · rw [pathWord, pathWord, ite_eq_left hch, ite_eq_left hch]
      exact ih J
    · rw [pathWord, pathWord, ite_eq_right hch, ite_eq_right hch]
      exact map_step φ _ _ _ _ ih J

theorem act_pathWord (hw : FactX2wedge) (hc : FactX2contr) {A : Type} [CommRing A] {n : ℕ}
    (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ) (Xc Xe : ℕ → Fin n → A)
    (g : (Matrix (Fin n) (Fin n) A)ˣ)
    (h1 : ∀ i, (isVec i == decide (1 ≤ c)) = true → Xe i = Matrix.vecMul (Xc i) (↑g : Matrix _ _ A))
    (h2 : ∀ i, (isVec i == decide (1 ≤ c)) = false →
      Xe i = Matrix.vecMul (Xc i) (↑g⁻¹ : Matrix _ _ A).transpose) :
    ∀ j : ℕ, pathWord isVec μ c Xe j = actF (pathWord isVec μ c Xc j) (↑g : Matrix _ _ A) := by
  intro j
  induction j with
  | zero => exact (actF_oneF _).symm
  | succ j ih =>
    by_cases hch : colHeight (μ (j + 1)) c = colHeight (μ j) c
    · rw [pathWord, pathWord, ite_eq_left hch, ite_eq_left hch]
      exact ih
    · rw [pathWord, pathWord, ite_eq_right hch, ite_eq_right hch, ih]
      unfold stepF
      cases hup : (isVec j == decide (1 ≤ c))
      · simp only [Bool.false_eq_true, ite_false]
        rw [hc, h2 j hup]
      · simp only [ite_true]
        rw [hw, h1 j hup]

end A1hw

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
