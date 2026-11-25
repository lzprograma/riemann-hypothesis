module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
public import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.WeilBound.ThetaLifts.LatticeBasics.EulerA
public import Mathlib.MeasureTheory.Measure.Haar.Unique
/-! # HaarMeasureTripleProductDecomposition: Preliminary helper declarations for global theta kernels. -/

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

theorem UpperTheory.haarMeasure_triple_product_decomposition :
    ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (A B C : Subgroup G), IsClosed (A : Set G) → IsClosed (B : Set G) → IsClosed (C : Set G) → ∀ (j : A × B × C ≃ₜ* G) (μ : Measure G), μ.IsHaarMeasure → ∀ (μA : Measure A) (μB : Measure B) (μC : Measure C), μA.IsHaarMeasure → μB.IsHaarMeasure → μC.IsHaarMeasure → ∀ f : G → ℂ, Integrable f μ → Integrable (fun y => f (j y)) (μA.prod (μB.prod μC)) ∧ ∃ c : ℝ, ∫ y, f (j y) ∂(μA.prod (μB.prod μC)) = c * ∫ g, f g ∂μ := by
  intro G _ _ _ _ _ _ _ _ A B C hA hB hC j μ hμ μA μB μC hμA hμB hμC f hf
  have : LocallyCompactSpace A := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace C := hC.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : (μB.prod μC).IsHaarMeasure := Measure.prod.instIsHaarMeasure μB μC
  have : SigmaFinite (μB.prod μC) := inferInstance
  have : MeasurableMul (B × C) := inferInstance
  have hPH : (μA.prod (μB.prod μC)).IsHaarMeasure :=
    Measure.prod.instIsHaarMeasure μA (μB.prod μC)
  set P : Measure (A × B × C) := μA.prod (μB.prod μC) with hP
  have hme : MeasurableEmbedding j := j.toHomeomorph.measurableEmbedding
  have hmap : (Measure.map j P).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map P j
  have hk : Measure.map j P = Measure.haarScalarFactor (Measure.map j P) μ • μ :=
    Measure.isMulLeftInvariant_eq_smul _ _
  set k : ℝ≥0 := Measure.haarScalarFactor (Measure.map j P) μ with hkdef
  have hfm : Integrable f (Measure.map j P) := by
    rw [hk]; exact hf.smul_measure (by simp)
  refine ⟨?_, (k : ℝ), ?_⟩
  · exact (hme.integrable_map_iff).1 hfm
  · have h1 : ∫ g, f g ∂(Measure.map j P) = ∫ y, f (j y) ∂P := hme.integral_map f
    rw [← h1, hk, integral_smul_nnreal_measure]
    simp [NNReal.smul_def]
