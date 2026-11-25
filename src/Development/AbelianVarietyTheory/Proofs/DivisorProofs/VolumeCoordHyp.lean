module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
private lemma mem_offHyp_iff {n : ℕ} {S : Finset (Fin n)}
    {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n} :
    v ∈ _root_.GlobalTheory.GoodTop.offHyp S U ↔ v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0 := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  exact Iff.rfl


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
lemma _root_.GlobalTheory.GoodTop.offHyp_ae_eq {n : ℕ} (S : Finset (Fin n))
    (U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) : _root_.GlobalTheory.GoodTop.offHyp S U =ᵐ[volume] U := by
  refine ae_eq_set.2 ⟨?_, ?_⟩
  · exact measure_mono_null
      (fun v hv => (hv.2 (mem_offHyp_iff.1 hv.1).1).elim) measure_empty
  · refine measure_mono_null (t := ⋃ a ∈ (S : Set (Fin n)), {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a = 0})
      ?_ ?_
    · intro v hv
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, exists_prop]
      by_contra! h
      exact hv.2 (mem_offHyp_iff.2 ⟨hv.1, h⟩)
    · refine (measure_biUnion_null_iff S.countable_toSet).2 fun a _ => ?_
      let L : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℝ] ℂ :=
        (EuclideanSpace.proj a : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).toLinearMap.restrictScalars ℝ
      have hset : {v : _root_.ReciprocityTheory.L2DbarEstimates.V n | v.ofLp a = 0} = (LinearMap.ker L : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) := by
        ext v
        simp [L]
      rw [hset]
      refine Measure.addHaar_submodule _ _ fun htop => ?_
      have hmem : EuclideanSpace.single a (1 : ℂ) ∈ LinearMap.ker L := htop ▸ Submodule.mem_top
      simp [L] at hmem

end GlobalTheory.GoodTop
