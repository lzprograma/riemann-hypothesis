module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.LocConstTensor

theorem exists_sum (Z : Type) [TopologicalSpace Z] [T2Space Z] (V : Type) [AddCommGroup V]
    [Module ℂ V] (T : Z → V) (hT : IsLocallyConstant T) (K : Set Z) (hK : IsCompact K)
    (h0 : ∀ y, y ∉ K → T y = 0) :
    ∃ (m : ℕ) (v : Fin m → V) (Φ : Fin m → SB Z), ∀ y, T y = ∑ i, (Φ i).1 y • v i := by
  classical
  have hfin : (T '' K).Finite := by
    letI : TopologicalSpace V := ⊥
    haveI : DiscreteTopology V := ⟨rfl⟩
    exact (hK.image hT.continuous).finite_of_discrete
  let S : Finset V := hfin.toFinset.erase 0
  let e : Fin S.card ≃ S := S.equivFin.symm
  have hmem : ∀ w : V, w ≠ 0 → (fun y => if T y = w then (1 : ℂ) else 0) ∈ SB Z := by
    intro w hw
    refine ⟨hT.comp (fun u => if u = w then (1 : ℂ) else 0), ?_⟩
    refine HasCompactSupport.intro hK ?_
    intro y hy
    rw [h0 y hy, ite_eq_right (Ne.symm hw)]
  refine ⟨S.card, fun i => (e i : V),
    fun i => ⟨_, hmem (e i) (Finset.ne_of_mem_erase (e i).2)⟩, fun y => ?_⟩
  have h1 : ∑ i, (if T y = (e i : V) then (1 : ℂ) else 0) • (e i : V)
      = ∑ w ∈ S, (if T y = w then (1 : ℂ) else 0) • w := by
    rw [← Finset.sum_coe_sort S]
    exact Equiv.sum_comp e (fun w : S => (if T y = (w : V) then (1 : ℂ) else 0) • (w : V))
  change T y = ∑ i, (if T y = (e i : V) then (1 : ℂ) else 0) • (e i : V)
  rw [h1]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    refine Finset.mem_erase.2 ⟨hne, hfin.mem_toFinset.2 ⟨y, ?_, rfl⟩⟩
    by_contra hy
    exact hne (h0 y hy)

end GlobalTheory.LocConstTensor
