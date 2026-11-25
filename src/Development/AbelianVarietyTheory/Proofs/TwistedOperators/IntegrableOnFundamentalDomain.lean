module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder

namespace GlobalTheory.CocompactIntegrable

theorem integrableOn_of_cocompact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : G, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (F : G → ℂ) (hF : Continuous F)
    (hinv : ∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) : IntegrableOn F 𝓕 μ := by
  have hle : μ 𝓕 ≤ μ C := by
    rw [h𝓕.measure_eq_tsum C]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    intro h hh
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hh⟩
  have hfin : μ 𝓕 ≠ ⊤ := (hle.trans_lt hC.measure_lt_top).ne
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  refine Measure.integrableOn_of_bounded (M := M) hfin hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
  rw [hinv γ hγ]
  exact hM c hc

theorem integrableOn_fundamentalDomain : ∀ {D : D7} (V : HSp D) (μ : Measure (GA D V)) (𝓕 C : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → IsCompact C → (∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c) → ∀ F : GA D V → ℂ, Continuous F → (∀ γ ∈ GQ V, ∀ h, F (γ * h) = F h) → IntegrableOn F 𝓕 μ := by
  intro D V μ 𝓕 C hμ h𝓕 hC hcov F hF hinv
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  exact integrableOn_of_cocompact (GQ V) μ 𝓕 C h𝓕 hC hcov F hF hinv

end GlobalTheory.CocompactIntegrable
