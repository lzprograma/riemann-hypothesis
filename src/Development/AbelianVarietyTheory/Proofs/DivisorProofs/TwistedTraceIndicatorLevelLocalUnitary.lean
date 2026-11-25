module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.TwTrUnit

theorem trace_eq_zero_of_finrank_eq_zero (W : Type) [AddCommGroup W] [Module ℂ W] (h : Module.finrank ℂ W = 0)
    (L : W →ₗ[ℂ] W) : LinearMap.trace ℂ W L = 0 := by
  by_cases hW : Module.Finite ℂ W
  · haveI : Subsingleton W := Module.finrank_zero_iff.1 h
    rw [show L = 0 from LinearMap.ext fun x => Subsingleton.elim _ _, map_zero]
  · unfold LinearMap.trace
    rw [dite_eq_right]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hW (Module.Finite.of_basis b)

theorem isHecke_indicator {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K K' : Subgroup G}
    (hK : IsCompact (K : Set G)) (ho : IsOpen (K' : Set G)) (hle : K' ≤ K) :
    IsHecke K' ((K' : Set G).indicator (1 : G → ℂ)) := by
  have hcl : IsClosed (K' : Set G) := K'.isClosed_of_isOpen ho
  have hc : IsCompact (K' : Set G) := hK.of_isClosed_subset hcl hle
  refine ⟨HasCompactSupport.intro' hc hcl fun x hx => Set.indicator_of_notMem hx _, fun k hk x => ⟨?_, ?_⟩⟩
  · have : k * x ∈ (K' : Set G) ↔ x ∈ (K' : Set G) := K'.mul_mem_cancel_left hk
    simp only [Set.indicator_apply, this, Pi.one_apply]
  · have : x * k ∈ (K' : Set G) ↔ x ∈ (K' : Set G) := K'.mul_mem_cancel_right hk
    simp only [Set.indicator_apply, this, Pi.one_apply]

theorem twTr_indicator {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K K' : Subgroup G) : twTr ρ K K' ((K' : Set G).indicator 1) LinearMap.id =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed ρ K') : ℂ) := by
  obtain ⟨x₀, hx₀, hL⟩ := GlobalTheory.TwTrLin.levOp_unit ρ K K'
  have hfx : ∀ v ∈ fixed ρ K', ρ x₀ v = v := fun v hv => (GlobalTheory.TwTrLin.mem_fixed_iff ρ K' v).1 hv x₀ hx₀
  have hm : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id v ∈ fixed ρ K' := by
    intro v hv
    rw [hL, LinearMap.smul_apply, hfx v hv]
    exact Submodule.smul_mem _ _ hv
  rw [GlobalTheory.TwTrLin.twTr_eq _ _ _ _ _ hm]
  have hr : (levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id).restrict hm =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
    ext x
    simp [LinearMap.restrict_apply, hL, hfx x.1 x.2]
  rw [hr, map_smul, GlobalTheory.TwTrLin.trace_id_eq_finrank, smul_eq_mul]

theorem twTr_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w)), IsLevel (MonoidHom.id (UL n w)) (KL n w) K' → ∀ σ : SmIrr (UL n w), IsHecke K' ((K' : Set (UL n w)).indicator 1) ∧ K'.relIndex (KL n w) ≠ 0 ∧ twTr σ.ρ (KL n w) K' ((K' : Set (UL n w)).indicator 1) LinearMap.id = ((K'.relIndex (KL n w) : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed σ.ρ K') : ℂ) ∧ (Module.finrank ℂ (fixed σ.ρ K') = 0 → ∀ g, twTr σ.ρ (KL n w) K' g LinearMap.id = 0) := by
  intro E _ _ _ n w K' hlev σ
  have hKc := GlobalTheory.LocFinU.isCompact_KL n w
  refine ⟨isHecke_indicator hKc hlev.1 hlev.2.1, GlobalTheory.TwTrLin.relIndex_ne_zero_of_isOpen hKc hlev.1,
    twTr_indicator _ _ _, fun h g => ?_⟩
  unfold twTr
  split_ifs with hm
  · exact trace_eq_zero_of_finrank_eq_zero _ h _
  · rfl

end GlobalTheory.TwTrUnit
