module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
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

open Filter Topology

namespace GlobalTheory.WeilM

theorem SB.exists_periodic {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] {ι : Type}
    (L : ι → AddSubgroup X) (hL : ∀ i, IsOpen (L i : Set X)) (hb : ∀ W ∈ 𝓝 (0 : X), ∃ i, (L i : Set X) ⊆ W) :
    ∀ f ∈ GlobalTheory.WeilM.SB X, ∃ i, ∀ Y, ∀ C ∈ L i, f (Y + C) = f Y := by
  intro f hf
  obtain ⟨hlc, hcs⟩ := hf
  have key : ∀ Y : X, ∃ i, ∀ C ∈ L i, f (Y + C) = f Y := by
    intro Y
    have h1 : f ⁻¹' {f Y} ∈ 𝓝 (Y + 0) := by rw [add_zero]; exact (hlc.isOpen_fiber _).mem_nhds rfl
    have h2 : {C : X | f (Y + C) = f Y} ∈ 𝓝 (0 : X) := (continuous_const_add Y).continuousAt.preimage_mem_nhds h1
    obtain ⟨i, hi⟩ := hb _ h2
    exact ⟨i, fun C hC => hi hC⟩
  choose g hg using key
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover (fun Y => {Z : X | Z - Y ∈ L (g Y)})
    (fun Y => (hL _).preimage (continuous_sub_right Y))
    (fun Z _ => Set.mem_iUnion.2 ⟨Z, by simp⟩)
  have hW : (⋂ Y ∈ t, (L (g Y) : Set X)) ∈ 𝓝 (0 : X) :=
    (Filter.biInter_finset_mem t).2 fun Y _ => (hL _).mem_nhds (L (g Y)).zero_mem
  obtain ⟨j, hj⟩ := hb _ hW
  refine ⟨j, fun Y C hC => ?_⟩
  have hCt : ∀ Y0 ∈ t, C ∈ L (g Y0) := fun Y0 h0 => by
    have := hj hC
    simp only [Set.mem_iInter] at this
    exact this Y0 h0
  by_cases h : ∃ Y0 ∈ t, Y - Y0 ∈ L (g Y0)
  · obtain ⟨Y0, h0, hY⟩ := h
    have e1 := hg Y0 _ hY
    have e2 := hg Y0 _ (add_mem hY (hCt Y0 h0))
    rw [show Y0 + (Y - Y0) = Y by abel] at e1
    rw [show Y0 + (Y - Y0 + C) = Y + C by abel] at e2
    rw [e1, e2]
  · push Not at h
    have hn : ∀ Z, Z ∈ tsupport f → ∃ Y0 ∈ t, Z - Y0 ∈ L (g Y0) := fun Z hZ => by
      have := ht hZ
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
      obtain ⟨Y0, h0, h1⟩ := this
      exact ⟨Y0, h0, h1⟩
    have hY : Y ∉ tsupport f := fun hZ => by
      obtain ⟨Y0, h0, h1⟩ := hn Y hZ
      exact h Y0 h0 h1
    have hYC : Y + C ∉ tsupport f := fun hZ => by
      obtain ⟨Y0, h0, h1⟩ := hn _ hZ
      apply h Y0 h0
      have := sub_mem h1 (hCt Y0 h0)
      rwa [show Y + C - Y0 - C = Y - Y0 by abel] at this
    rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hYC]

end GlobalTheory.WeilM
