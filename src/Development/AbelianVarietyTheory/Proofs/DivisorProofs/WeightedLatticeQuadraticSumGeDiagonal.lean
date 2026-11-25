module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosSemidefOfIntForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.StarInvMulVecDotProductMulVecInvMulVec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.QWDom

open Matrix in
theorem exists_pos_posSemidef_sub_smul_one {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ (A - c • (1 : Matrix n n ℝ)).PosSemidef := by
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ hA.1.eigenvalues i := by
    rcases isEmpty_or_nonempty n with h | h
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ hA.1.eigenvalues Finset.univ_nonempty
      exact ⟨_, hA.eigenvalues_pos i0, fun i => hi0 i (Finset.mem_univ _)⟩
  refine ⟨c, hc, ?_⟩
  have hs := hA.1.spectral_theorem
  have h1 : c • (1 : Matrix n n ℝ) = Unitary.conjStarAlgAut ℝ _ hA.1.eigenvectorUnitary (c • 1) := by
    rw [map_smul, map_one]
  rw [h1]
  conv => arg 1; arg 1; rw [hs]
  rw [← map_sub, Unitary.conjStarAlgAut_apply]
  rw [Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff]
  rw [smul_one_eq_diagonal, diagonal_sub]
  exact PosSemidef.diagonal fun i => by simpa using hle i

open Matrix in
theorem gram_nonneg_int {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y)
    (y : Fin s → X) (z : Fin s → ℤ) : 0 ≤ ∑ u, ∑ v, z u * β (y u) (y v) * z v := by
  have h := hβ (∑ u, z u • y u)

  simp only [map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply, smul_eq_mul] at h
  have e : ∑ u, ∑ v, z u * β (y u) (y v) * z v = ∑ x, z x * ∑ x1, z x1 * β (y x1) (y x) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [e]; exact h

open Matrix in
theorem gram_nonneg_rat {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (hβ : ∀ y, 0 ≤ β y y)
    (y : Fin s → X) (q : Fin s → ℚ) :
    0 ≤ ∑ u, ∑ v, (q u : ℝ) * (β (y u) (y v) : ℝ) * (q v : ℝ) := by
  set D : ℕ := ∏ u, (q u).den with hD
  have hDpos : (0 : ℝ) < D := by
    have : 0 < D := Finset.prod_pos fun u _ => (q u).den_pos
    exact_mod_cast this
  have hz : ∀ u, ∃ z : ℤ, (q u : ℝ) * D = z := by
    intro u
    obtain ⟨k, hk⟩ : (q u).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ u)
    refine ⟨(q u).num * k, ?_⟩
    rw [hk]
    have hq : (q u : ℝ) = (q u).num / (q u).den := by exact_mod_cast (Rat.num_div_den (q u)).symm
    have hd : ((q u).den : ℝ) ≠ 0 := by exact_mod_cast (q u).den_nz
    rw [hq]; push_cast; field_simp
  choose z hz using hz
  have h0 : (0 : ℝ) ≤ ∑ u, ∑ v, (z u : ℝ) * (β (y u) (y v) : ℝ) * (z v : ℝ) := by
    exact_mod_cast gram_nonneg_int β hβ y z
  have : ∑ u, ∑ v, (z u : ℝ) * (β (y u) (y v) : ℝ) * (z v : ℝ) =
      (D : ℝ) ^ 2 * ∑ u, ∑ v, (q u : ℝ) * (β (y u) (y v) : ℝ) * (q v : ℝ) := by
    simp only [← hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [this] at h0
  exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h0

open Matrix in
theorem gram_posSemidef {s : ℕ} {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hsym : ∀ a b, β a b = β b a) (hβ : ∀ y, 0 ≤ β y y) (y : Fin s → X) :
    (Matrix.of fun u v => (β (y u) (y v) : ℝ)).PosSemidef := by
  intros
  apply _root_.GlobalTheory.gram_posSemidef_of_int_form <;> assumption

open Matrix in
theorem qW_ge : ∀ (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ), PosW W → ∃ c : ℝ, 0 < c ∧ ∀ (X : Type) [AddCommGroup X] (β : LinearMap.BilinForm ℤ X), (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ y : Fin s → X, c * (∑ u, β (y u) (y u) : ℤ) ≤ (qW W β y : ℤ) := by
  intro s W hW
  obtain ⟨c, hc, hP⟩ := exists_pos_posSemidef_sub_smul_one hW
  refine ⟨c / 2, by positivity, fun X _ β hsym hβ y => ?_⟩
  have hM := gram_posSemidef β hsym hβ y
  have ht := GlobalTheory.trace_mul_nonneg_of_posSemidef hP hM
  rw [Matrix.sub_mul, trace_sub, Matrix.smul_mul, Matrix.one_mul, trace_smul, sub_nonneg] at ht
  simp only [trace, diag, Matrix.mul_apply, Matrix.map_apply, Matrix.add_apply, transpose_apply, Matrix.of_apply,
    smul_eq_mul] at ht
  have e : ∑ u, ∑ v, ((W u v + W v u : ℤ) : ℝ) * (β (y v) (y u) : ℝ) = 2 * (qW W β y : ℝ) := by
    simp only [qW, Int.cast_sum, Int.cast_mul, Int.cast_add, add_mul, Finset.sum_add_distrib]
    rw [two_mul]
    congr 1
    · refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [hsym]
    · rw [Finset.sum_comm]
  push_cast at ht e ⊢
  linarith

end GlobalTheory.Poinc.QWDom
