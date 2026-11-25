module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsOpenLevelNormalizedByIntegralFiniteGL
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Translation
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

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct

theorem UpperTheory.exists_finiteDimensional_compact_translates_of_level_types :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Level S → Types S → ∃ V : Submodule ℂ (Reduction.maxCompact (K := K) (n := n) → ℂ), FiniteDimensional ℂ V ∧ ∀ φ ∈ S, ∀ g, (fun k : Reduction.maxCompact (K := K) (n := n) => φ.1 (g * k.1)) ∈ V := by
  intro K _ _ n S hLev hTyp
  obtain ⟨L, hL, hinv⟩ := hLev
  obtain ⟨V₀, hV₀, -, hφV⟩ := hTyp
  obtain ⟨L', -, hL'L, -, t, ht⟩ := UpperTheory.exists_open_level_normalized_by_integralFiniteGL K n L hL
  have hk : ∀ k : Reduction.maxCompact (K := K) (n := n), ∃ c ∈ t, c⁻¹ * finPart k.1 ∈ L' :=
    fun k => ht _ (finPart_mem_integralFiniteGL k.2)
  let Ψ : (↥t → ↥V₀) →ₗ[ℂ] (Reduction.maxCompact (K := K) (n := n) → ℂ) :=
    { toFun := fun h k =>
        (h ⟨Classical.choose (hk k), (Classical.choose_spec (hk k)).1⟩ : archCompact K n → ℂ)
          ⟨archPart k.1, archPart_mem_archCompact k.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  refine ⟨LinearMap.range Ψ, inferInstance, ?_⟩
  intro φ hφ g
  refine ⟨fun c => ⟨fun k' => φ.1 (g * finEmb K n c.1 * infEmb K n k'.1), hφV φ hφ _⟩, ?_⟩
  funext k
  show φ.1 (g * finEmb K n (Classical.choose (hk k)) * infEmb K n (archPart k.1)) = φ.1 (g * k.1)
  have hu : (Classical.choose (hk k))⁻¹ * finPart k.1 ∈ L := hL'L (Classical.choose_spec (hk k)).2
  have e : g * k.1 = g * finEmb K n (Classical.choose (hk k)) * infEmb K n (archPart k.1) *
      finEmb K n ((Classical.choose (hk k))⁻¹ * finPart k.1) := by
    conv_lhs => rw [← infEmb_archPart_mul_finEmb_finPart k.1]
    rw [map_mul, map_inv, mul_assoc g (finEmb K n _), ← infEmb_mul_finEmb_comm]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [e, hinv φ hφ _ hu]
