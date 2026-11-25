module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
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
import Mathlib.Tactic.Linter.Style
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx


open GlobalTheory.SplitWeil.FourierPi in
theorem exists_SB_supported_integral_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (U : Set (n → k)) (_ : U ∈ nhds (0 : n → k)), ∃ Ψ : SB (n → k), (∀ y, y ∉ U → Ψ.1 y = 0) ∧ ∫ y, Ψ.1 y ∂(Measure.pi fun _ => ν) = 1 := by
  intro k _ _ _ _ _ _ n _ _ ν _ U hU
  have := GlobalTheory.SplitWeil.secondCountable k
  have := sigmaCompactSpace_of_locallyCompact_secondCountable (X := k)
  obtain ⟨s, hsU⟩ := exists_box_subset (k := k) (n := n) hU
  have hBo : IsOpen (box (k := k) n s) := isOpen_box s
  have hBc : IsCompact (box (k := k) n s) := isCompact_box s
  have hBcl : IsClosed (box (k := k) n s) := isClosed_set_pi fun _ _ =>
    AddSubgroup.isClosed_of_isOpen
      { carrier := cball s
        zero_mem' := by
          show valuation k (0 : k) ≤ valuation k (s : k)
          rw [map_zero]
          exact zero_le
        add_mem' := add_mem_cball
        neg_mem' := neg_mem_cball } (isOpen_cball s)
  have hBm : MeasurableSet (box (k := k) n s) :=
    MeasurableSet.univ_pi fun _ => (isOpen_cball s).measurableSet
  have h0 : (0 : n → k) ∈ box (k := k) n s := by
    intro i _
    show valuation k (0 : k) ≤ valuation k (s : k)
    rw [map_zero]
    exact zero_le
  have hpos : 0 < (Measure.pi fun _ : n => ν) (box n s) := hBo.measure_pos _ ⟨0, h0⟩
  have hfin : (Measure.pi fun _ : n => ν) (box n s) < ⊤ := hBc.measure_lt_top
  have hreal : (Measure.pi fun _ : n => ν).real (box n s) ≠ 0 :=
    (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  set c : ℂ := (((Measure.pi fun _ : n => ν).real (box n s) : ℝ) : ℂ)⁻¹ with hc
  refine ⟨⟨(box (k := k) n s).indicator fun _ => c,
    (LocallyConstant.indicator (LocallyConstant.const _ c) ⟨hBcl, hBo⟩).isLocallyConstant,
    HasCompactSupport.intro' hBc hBcl fun y hy => Set.indicator_of_notMem hy _⟩, ?_, ?_⟩
  · intro y hy
    show (box (k := k) n s).indicator (fun _ => c) y = 0
    exact Set.indicator_of_notMem (fun hb => hy (hsU hb)) _
  · show ∫ y, (box (k := k) n s).indicator (fun _ => c) y ∂(Measure.pi fun _ => ν) = 1
    rw [integral_indicator_const c hBm, Complex.real_smul, hc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hreal)]

end GlobalTheory.RootEx
