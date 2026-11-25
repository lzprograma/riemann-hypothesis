module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesTranslateNormLe
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEllipticFunctionMulProdEqXy
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralWeierstrassChartXyUnitSeries
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.EllBdd

variable {q : ℕ} [Fact q.Prime]

theorem bd_C (a : ℂ_[q]) : Bd ‖a‖ (C a : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs <;> simp

theorem bd_mono {A B : ℝ} {f : ℂ_[q]⟦X⟧} (h : Bd A f) (hAB : A ≤ B) : Bd B f :=
  fun n => (h n).trans hAB

theorem bd_X_pow (k : ℕ) : Bd 1 (X ^ k : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_X_pow]
  split_ifs <;> simp

theorem bd_one_add {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f + g) := by
  simpa using ((sup_norm_laws q).1 f g 1 1 hf hg).1

theorem bd_one_sum {α : Type*} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) (h : ∀ i ∈ s, Bd 1 (f i)) :
    Bd 1 (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Bd 1) (fun _ _ => bd_one_add) (fun n => by simp) h

theorem bdd_mul {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f * g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hA hB).2⟩

theorem bdd_add {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hA hB).1⟩

theorem bdd_sum {α : Type*} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) (h : ∀ i ∈ s, Bdd (f i)) :
    Bdd (∑ i ∈ s, f i) :=
  Finset.sum_induction f Bdd (fun _ _ => bdd_add) ⟨0, fun n => by simp⟩ h

theorem hat_one (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hℓ : constantCoeff ℓ = 0) :
    hat ι ℓ (fun _ => 1) = 1 := by
  have h1 : tay (fun _ => 1) = 1 := by
    ext n
    rw [tay, coeff_mk, coeff_one, iteratedDeriv_const]
    split_ifs with h
    · simp [h]
    · simp
  have hs : HasSubst ℓ := HasSubst.of_constantCoeff_zero' hℓ
  rw [hat, h1, map_one, ← coe_substAlgHom hs, map_one]

theorem bdd_hat_of_ell : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → Bdd (hat M.ι ℓ φ) := by
  intro q _ M ℓ φ hC hE hA hP
  obtain ⟨m, P, A, B, hPi, hz⟩ := GlobalTheory.EllipticModel.exists_mul_prod_eq_xy q M φ hC.1 hE
  obtain ⟨-, v, xs, ys, -, hxs, hys, -, hx0, -, -, -, -, hmain⟩ := GlobalTheory.MomOne.ChartXY.chart_xy q M ℓ hC
  set D : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hD
  have hmon : D.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hdeg : D.natDegree = m := by
    rw [hD, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have hint : ∀ n, ‖M.ι (D.coeff n)‖ ≤ 1 := by
    refine GlobalTheory.MomOne.TransNorm.norm_coeff_prod M.ι (fun i => M.x (P i)) fun i => ?_
    by_contra h
    exact hP _ (hPi i).2 (Or.inr (not_le.mp h))
  have key := hmain φ A B (max A.natDegree B.natDegree) hA (le_max_left _ _) (le_max_right _ _)
    (fun _ => 1) analyticAt_const D m hdeg.le (by simpa using hz 0)
  set k := max A.natDegree B.natDegree
  set S := ∑ i ∈ Finset.range (m + 1), C (M.ι (D.coeff i)) * X ^ (2 * (m - i)) * xs ^ i with hS
  have hS1 : Bd 1 S := bd_one_sum _ _ fun i _ =>
    GlobalTheory.MomOne.Triang.bd_one_mul (GlobalTheory.MomOne.Triang.bd_one_mul (bd_mono (bd_C _) (hint i)) (bd_X_pow _)) (GlobalTheory.MomOne.Triang.bd_one_pow hxs i)
  have hS0 : ‖constantCoeff S‖ = 1 := by

    rw [hS, Finset.sum_range_succ, map_add (f := _), map_sum, Finset.sum_eq_zero, zero_add]
    · have : D.coeff m = 1 := by rw [← hdeg]; exact hmon.coeff_natDegree
      simp [this, hx0]
    · intro i hi
      have : 2 * (m - i) ≠ 0 := by have := Finset.mem_range.mp hi; omega
      simp [this]
  have hR : Bdd (hat M.ι ℓ φ * X ^ (2 * k + 3) * S) := by
    rw [key, hat_one M.ι ℓ hC.2.1, one_mul]
    refine bdd_mul ⟨_, bd_X_pow _⟩ (bdd_sum _ _ fun i _ => bdd_add ?_ ?_)
    · exact bdd_mul (bdd_mul ⟨_, bd_C _⟩ ⟨_, bd_X_pow _⟩) ⟨_, GlobalTheory.MomOne.Triang.bd_one_pow hxs i⟩
    · exact bdd_mul (bdd_mul (bdd_mul ⟨_, bd_C _⟩ ⟨_, bd_X_pow _⟩) ⟨_, GlobalTheory.MomOne.Triang.bd_one_pow hxs i⟩) ⟨_, hys⟩
  obtain ⟨R, hR⟩ := hR
  refine ⟨R, (sup_norm_laws q).2.2.2.2.2 _ S (2 * k + 3) R hS1 hS0 ?_⟩
  rwa [show X ^ (2 * k + 3) * S * hat M.ι ℓ φ = hat M.ι ℓ φ * X ^ (2 * k + 3) * S by ring]

end GlobalTheory.MomOne.EllBdd
