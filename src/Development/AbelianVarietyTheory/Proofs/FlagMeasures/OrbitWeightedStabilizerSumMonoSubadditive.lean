module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.OrbMono

theorem orbSum_eq (G α : Type) [Group G] [MulAction G α] (X : Set α) (N : α → ℝ≥0∞) :
    orbSum G X N = ∑' q : MulAction.orbitRel.Quotient G α,
      if Quotient.out q ∈ X then
        ((ENat.card (MulAction.stabilizer G (Quotient.out q)) : ℕ∞) : ℝ≥0∞)⁻¹ * N (Quotient.out q)
      else 0 := by
  exact (tsum_subtype {q : MulAction.orbitRel.Quotient G α | Quotient.out q ∈ X}
    (fun q => ((ENat.card (MulAction.stabilizer G (Quotient.out q)) : ℕ∞) : ℝ≥0∞)⁻¹ *
      N (Quotient.out q))).trans (tsum_congr fun q => by simp [Set.indicator_apply])

theorem main : ∀ (G α : Type) [Group G] [MulAction G α] , (∀ (X Y : Set α) (N N' : α → ℝ≥0∞), X ⊆ Y → (∀ x ∈ X, N x ≤ N' x) → orbSum G X N ≤ orbSum G Y N') ∧ (∀ (X : Set α) (B : ℝ≥0∞), orbSum G X (fun _ => B) = B * orbMass G X) ∧ (∀ (ι : Type) (s : Finset ι) (X : Set α) (Xi : ι → Set α) (N : α → ℝ≥0∞), X ⊆ ⋃ i ∈ s, Xi i → orbSum G X N ≤ ∑ i ∈ s, orbSum G (Xi i) N) ∧ (∀ (X : Set α) (s : Set α), (∀ x ∈ X, ∃ y ∈ s, ∃ g : G, g • y = x) → orbMass G X ≤ ((s.encard : ℕ∞) : ℝ≥0∞)) ∧ (∀ (X : Set α) (N N' : α → ℝ≥0∞), orbSum G X (fun x => N x + N' x) = orbSum G X N + orbSum G X N') := by
  intro G α _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X Y N N' hXY hN
    simp only [orbSum_eq]
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hq : Quotient.out q ∈ X
    · rw [ite_eq_left hq, ite_eq_left (hXY hq)]
      gcongr
      exact hN _ hq
    · rw [ite_eq_right hq]
      exact zero_le
  · intro X B
    simp only [orbMass, orbSum]
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun q => by rw [mul_one, mul_comm]
  · intro ι s X Xi N hX
    simp only [orbSum_eq]
    rw [← Summable.tsum_finsetSum (fun i _ => ENNReal.summable)]
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hq : Quotient.out q ∈ X
    · obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.1 (hX hq)
      refine le_trans ?_ (Finset.single_le_sum (fun j _ => zero_le) hi)
      simp [hq, hqi]
    · rw [ite_eq_right hq]
      exact zero_le
  · intro X s hs
    have key : ∀ q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
        ∃ y : s, (Quotient.mk _ (y : α) : MulAction.orbitRel.Quotient G α) = q.1 := by
      rintro ⟨q, hq⟩
      obtain ⟨y, hy, g, hg⟩ := hs _ hq
      refine ⟨⟨y, hy⟩, ?_⟩
      exact (Quotient.sound (MulAction.orbitRel_apply.2 ⟨g⁻¹, by simp [← hg]⟩)).trans
        (Quotient.out_eq q)
    choose φ hφ using key
    have hinj : Function.Injective φ := by
      intro a b h
      apply Subtype.ext
      rw [← hφ a, ← hφ b, h]
    calc orbMass G X
        = ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
            ((ENat.card (MulAction.stabilizer G (Quotient.out q.1)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1 := rfl
      _ ≤ ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
            (fun _ : s => (1 : ℝ≥0∞)) (φ q) := by
          refine ENNReal.tsum_le_tsum fun q => ?_
          rw [mul_one]
          apply ENNReal.inv_le_one.2
          have h1 : (1 : ℕ∞) ≤ ENat.card (MulAction.stabilizer G (Quotient.out q.1)) :=
            (ENat.one_le_card_iff_nonempty _).2 ⟨1⟩
          exact_mod_cast h1
      _ ≤ ∑' _ : s, (1 : ℝ≥0∞) := (by refine' _root_.le_trans _ (_root_.tsum_comp_le_tsum_of_injective hinj _); exact _root_.le_rfl)
      _ = s.encard := ENNReal.tsum_set_one s
  · intro X N N'
    simp only [orbSum]
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun q => mul_add _ _ _

end GlobalTheory.Mass.OrbMono
