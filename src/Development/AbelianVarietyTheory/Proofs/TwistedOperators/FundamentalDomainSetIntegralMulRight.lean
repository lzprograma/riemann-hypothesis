module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory

theorem fundamentalDomain_setIntegral_mul_right :
    ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ k : G, Measure.map (fun g => g * k) μ = μ → ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ → IntegrableOn (fun g => f (g * k)) 𝓕 μ ∧ ∫ g in 𝓕, f (g * k) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  intro G _ _ _ _ Γ _ μ _ 𝓕 h𝓕 k hk f hf hi
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ (γ : Γ) (g : G), (fun g : G => f (g * k)) (γ • g) = (fun g : G => f (g * k)) g := by
    intro γ g
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  refine ⟨?_, ?_⟩
  · rw [h𝓕.integrableOn_iff h2 hinv]
    exact (hmp.integrableOn_comp_preimage hemb).2 hi
  · rw [h𝓕.setIntegral_eq h2 hinv]
    exact hmp.setIntegral_preimage_emb hemb f 𝓕

end GlobalTheory
