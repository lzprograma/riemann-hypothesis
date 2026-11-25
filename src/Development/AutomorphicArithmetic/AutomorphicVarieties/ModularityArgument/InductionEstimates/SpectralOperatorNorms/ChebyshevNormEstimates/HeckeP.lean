module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.ContinuousLeviUnipotentPath
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.FlatInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAdj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem map_inv_self {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (ν : Measure G) [IsProbabilityMeasure ν] (U : Subgroup G) (hs : ∀ᵐ k ∂ν, k ∈ U)
    (hi : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν) : ν.map (fun k => k⁻¹) = ν := by
  apply _root_.inv_map <;> assumption

private theorem hecke_star {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n) (f : CC K n)
    (hf : D.Hecke f) : D.Hecke (CuspidalProjection.ccStar f) := by
  apply _root_.star_hecke <;> assumption

private theorem half_P {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P Y : H →L[ℂ] H) (hP : IsOrthogonalProjectionTwoLines J J' P)
    (h : ∀ u, ∃ u', ContinuousLinearMap.adjoint Y (J u) = J u')
    (h' : ∀ u, ∃ u', ContinuousLinearMap.adjoint Y (J' u) = J' u') : P ∘L Y = P ∘L Y ∘L P := by
  ext x
  have h0 : P (x - P x) = 0 := by
    have := congrArg (fun T : H →L[ℂ] H => T x) hP.2.1
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [map_sub, this, sub_self]
  have h1 := (hP.2.2 _).1 h0
  have h2 : P (Y (x - P x)) = 0 := by
    refine (hP.2.2 _).2 ⟨fun u => ?_, fun u => ?_⟩
    · obtain ⟨u', hu⟩ := h u
      rw [← ContinuousLinearMap.adjoint_inner_left, hu, h1.1]
    · obtain ⟨u', hu⟩ := h' u
      rw [← ContinuousLinearMap.adjoint_inner_left, hu, h1.2]
  rw [map_sub, map_sub, sub_eq_zero] at h2
  simpa using h2

private theorem comm_P {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (P Y : H →L[ℂ] H) (hP : IsOrthogonalProjectionTwoLines J J' P)
    (g : ∀ u, ∃ u', Y (J u) = J u') (g' : ∀ u, ∃ u', Y (J' u) = J' u')
    (h : ∀ u, ∃ u', ContinuousLinearMap.adjoint Y (J u) = J u')
    (h' : ∀ u, ∃ u', ContinuousLinearMap.adjoint Y (J' u) = J' u') : Y ∘L P = P ∘L Y := by
  have a := half_P J J' P Y hP h h'
  have b := half_P J J' P (ContinuousLinearMap.adjoint Y) hP
    (by simpa only [ContinuousLinearMap.adjoint_adjoint] using g)
    (by simpa only [ContinuousLinearMap.adjoint_adjoint] using g')
  have hs : ContinuousLinearMap.adjoint P = P := hP.1.adjoint_eq
  have c := congrArg ContinuousLinearMap.adjoint b
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hs] at c
  exact c.trans ((ContinuousLinearMap.comp_assoc _ _ _).trans a.symm)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Hecke₃ :
    ForAllC fun K _ _ μ _ _ _ _ _ D _ _ A A' => ∀ P, IsOrthogonalProjectionTwoLines A.J A'.J P →
      (∀ Y : L2 μ →L[ℂ] L2 μ, (∀ u, ∃ u', Y (A.J u) = A.J u') → (∀ u, ∃ u', Y (A'.J u) = A'.J u') →
        (∀ u, ∃ u', ContinuousLinearMap.adjoint Y (A.J u) = A.J u') → (∀ u, ∃ u', ContinuousLinearMap.adjoint Y (A'.J u) = A'.J u') → Y ∘L P = P ∘L Y) ∧
      ∀ f : CC K (2 + 2), D.Hecke f → Rop μ f ∘L P = P ∘L Rop μ f := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' P hP
  refine ⟨fun Y => comm_P A.J A'.J P Y hP, fun f hf => ?_⟩
  have k1 : ∀ f : CC K (2 + 2), D.Hecke f → ∀ u, ∃ u', Rop μ f (A.J u) = A.J u' := fun f hf u => by
    obtain ⟨β, hb⟩ := convR K μ μ₂ τ₁ τ₂ hp D d d' A A' f hf
    exact ⟨_, hb.2.1 u _ (convSpec β hb.1 u).1⟩
  have k2 : ∀ f : CC K (2 + 2), D.Hecke f → ∀ u, ∃ u', Rop μ f (A'.J u) = A'.J u' := fun f hf u => by
    obtain ⟨β, hb⟩ := convR K μ μ₂ τ₂ τ₁ ⟨hp.irr₂, hp.irr₁, hp.orth.symm⟩ D d' d A' A f hf
    exact ⟨_, hb.2.1 u _ (convSpec β hb.1 u).1⟩
  refine comm_P A.J A'.J P _ hP (k1 f hf) (k2 f hf) ?_ ?_
  · rw [UpperTheory.ConvolutionTheory.K.ropAdj]; exact k1 _ (hecke_star D f hf)
  · rw [UpperTheory.ConvolutionTheory.K.ropAdj]; exact k2 _ (hecke_star D f hf)
