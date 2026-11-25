module

public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
import GroundTheory.AutomorphicForms.ReductionMeasure
import GroundTheory.GlobalFields.Adele.Topology
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct

private theorem cont_setIntegral {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    (μ : Measure Y) (f : X → Y → ℂ) (hf : Continuous f.uncurry) {s C : Set Y} (hs : MeasurableSet s)
    (hC : IsCompact C) (hsC : s ⊆ C) (hμ : μ s < ⊤) (hi : ∀ x, IntegrableOn (f x) s μ) :
    Continuous fun x => ∫ y in s, f x y ∂μ := by
  refine continuous_iff_continuousAt.2 fun x₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hm : 0 ≤ (μ s).toReal := ENNReal.toReal_nonneg
  have hδ : 0 < ε / ((μ s).toReal + 1) := div_pos hε (by linarith)
  have hc : Continuous fun z : X × Y => f z.1 z.2 - f x₀ z.2 :=
    hf.sub (hf.comp (Continuous.prodMk continuous_const continuous_snd))
  have htube : ∀ᶠ x in nhds x₀, ∀ y ∈ C, ‖f x y - f x₀ y‖ < ε / ((μ s).toReal + 1) := by
    apply hC.eventually_forall_of_forall_eventually
    intro y _
    exact (hc.norm.tendsto (x₀, y)).eventually (gt_mem_nhds (by simpa using hδ))
  filter_upwards [htube] with x hx
  rw [dist_eq_norm, ← integral_sub (hi x) (hi x₀)]
  calc ‖∫ y in s, (f x y - f x₀ y) ∂μ‖ ≤ ε / ((μ s).toReal + 1) * (μ s).toReal :=
        norm_setIntegral_le_of_norm_le_const hμ (fun y hy => (hx y (hsC hy)).le)
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

theorem UpperTheory.continuous_constantTerm :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ),
      Continuous φ → Continuous (constantTerm (r := r) φ) := by
  intro K _ _ n r φ hφ
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  exact cont_setIntegral (unipMeasure K n r) (fun g X => φ (unipGL X * g))
    (hφ.comp ((continuous_unipGL.comp continuous_snd).mul continuous_fst))
    measurableSet_unipFundamentalDomain hC hDC ((measure_mono hDC).trans_lt hC.measure_lt_top)
    (fun g => integrableOn_constantTerm hφ g)
