module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory

theorem sqOpen_of_two_ne_zero : ∀ (K : Type) [NormedField K] [CompleteSpace K], (2 : K) ≠ 0 → SqOpen K := by
  intro K _ _ h2 V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  set c := ‖(2:K)⁻¹‖ with hc
  set ρ := min (ε / 2) (1 / (4 * c + 1)) with hρ
  have hρ0 : 0 < ρ := lt_min (by linarith) (by positivity)
  have hρε : ρ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρc : 2 * ρ * c ≤ 1 / 2 := by
    have h1 : ρ ≤ 1 / (4 * c + 1) := min_le_right _ _
    have h4 : 0 < 4 * c + 1 := by positivity
    have h5 : ρ * (4 * c + 1) ≤ 1 := by rwa [le_div_iff₀ h4] at h1
    nlinarith
  set δ := ρ / (2 * c + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hcδ : c * δ ≤ ρ / 2 := by
    have h : 0 < 2 * c + 1 := by positivity
    have h' : δ * (2 * c + 1) = ρ := div_mul_cancel₀ _ (ne_of_gt h)
    nlinarith
  refine ⟨Metric.closedBall 1 δ, Metric.closedBall_mem_nhds _ hδ0, ?_⟩
  intro r hr
  have hr' : ‖r - 1‖ ≤ δ := by simpa [dist_eq_norm] using hr
  set f : K → K := fun μ => μ - (μ ^ 2 - r) * (2:K)⁻¹ with hfdef
  have h22 : (2:K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hdiff : ∀ μ₁ μ₂ : K, f μ₁ - f μ₂ = (μ₁ - μ₂) * ((1 - μ₁) + (1 - μ₂)) * (2:K)⁻¹ := by
    intro μ₁ μ₂
    simp only [hfdef]
    linear_combination (-(μ₁ - μ₂)) * h22
  have hf1 : f 1 - 1 = (r - 1) * (2:K)⁻¹ := by
    simp only [hfdef]; ring
  set s := Metric.closedBall (1:K) ρ with hs
  have hlip : ∀ μ₁ ∈ s, ∀ μ₂ ∈ s, ‖f μ₁ - f μ₂‖ ≤ (1 / 2) * ‖μ₁ - μ₂‖ := by
    intro μ₁ h1 μ₂ h2'
    rw [hdiff, norm_mul, norm_mul]
    have a1 : ‖1 - μ₁‖ ≤ ρ := by
      rw [norm_sub_rev]; simpa [hs, dist_eq_norm] using h1
    have a2 : ‖1 - μ₂‖ ≤ ρ := by
      rw [norm_sub_rev]; simpa [hs, dist_eq_norm] using h2'
    have a3 : ‖(1 - μ₁) + (1 - μ₂)‖ ≤ 2 * ρ := (norm_add_le _ _).trans (by linarith)
    calc ‖μ₁ - μ₂‖ * ‖(1 - μ₁) + (1 - μ₂)‖ * c ≤ ‖μ₁ - μ₂‖ * (2 * ρ) * c := by gcongr
      _ = ‖μ₁ - μ₂‖ * (2 * ρ * c) := by ring
      _ ≤ ‖μ₁ - μ₂‖ * (1 / 2) := by gcongr
      _ = (1 / 2) * ‖μ₁ - μ₂‖ := by ring
  have h1s : (1:K) ∈ s := Metric.mem_closedBall_self hρ0.le
  have hmaps : Set.MapsTo f s s := by
    intro μ hμ
    have hl := hlip μ hμ 1 h1s
    have hμ' : ‖μ - 1‖ ≤ ρ := by simpa [hs, dist_eq_norm] using hμ
    have hf1' : ‖f 1 - 1‖ ≤ c * δ := by
      rw [hf1, norm_mul, mul_comm]; gcongr
    have key : ‖f μ - 1‖ ≤ ρ := by
      calc ‖f μ - 1‖ = ‖(f μ - f 1) + (f 1 - 1)‖ := by congr 1; ring
        _ ≤ ‖f μ - f 1‖ + ‖f 1 - 1‖ := norm_add_le _ _
        _ ≤ (1 / 2) * ρ + c * δ := by gcongr; exact hl.trans (by gcongr)
        _ ≤ ρ := by linarith
    simpa [hs, dist_eq_norm] using key
  have hcomplete : IsComplete s := Metric.isClosed_closedBall.isComplete
  have hcon : ContractingWith (1 / 2 : NNReal) (hmaps.restrict f s s) := by
    constructor
    · rw [← NNReal.coe_lt_coe]; push_cast; norm_num
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Set.MapsTo.val_restrict_apply, Subtype.dist_eq, dist_eq_norm]
      push_cast
      exact hlip _ x.2 _ y.2
  obtain ⟨μ, hμs, hfix, -⟩ :=
    hcon.exists_fixedPoint' hcomplete hmaps h1s (edist_ne_top _ _)
  refine ⟨μ, hball (Metric.closedBall_subset_ball hρε hμs), ?_⟩
  have hfix' : f μ = μ := hfix
  have hz : (μ ^ 2 - r) * (2:K)⁻¹ = 0 := by
    simp only [hfdef] at hfix'
    linear_combination -hfix'
  rcases mul_eq_zero.1 hz with h | h
  · linear_combination h
  · exact absurd h (inv_ne_zero h2)

end GlobalTheory
