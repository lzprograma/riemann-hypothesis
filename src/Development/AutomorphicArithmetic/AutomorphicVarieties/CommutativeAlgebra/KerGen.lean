module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.RingTheory.Filtration

@[expose] public section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem ker_gen_closed {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A)
    (f : A) (h : ∀ N : ℕ, ∃ g ∈ I, f - g ∈ maximalIdeal A ^ N) : f ∈ I := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ I) (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
  have hmem : Ideal.Quotient.mk I f ∈ ⨅ i, (maximalIdeal A) ^ i • (⊤ : Submodule A (A ⧸ I)) := by
    rw [Submodule.mem_iInf]
    intro N
    obtain ⟨g, hg, hfg⟩ := h N
    have heq : Ideal.Quotient.mk I f = (f - g) • (1 : A ⧸ I) := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one, map_sub,
        Ideal.Quotient.eq_zero_iff_mem.mpr hg, sub_zero]
    rw [heq]
    exact Submodule.smul_mem_smul hfg Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

private theorem ker_gen_approx {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X]
    {σ : Type} [Finite σ] (wt : σ → X) (f : MvPowerSeries σ O) (N : ℕ) :
    ∃ T : Finset X, f - ∑ j ∈ T, wcomp O wt j f ∈ maximalIdeal (MvPowerSeries σ O) ^ N := by
  classical
  set D := (Finsupp.finite_of_degree_lt (σ := σ) N).toFinset with hD
  refine ⟨D.image (Finsupp.weight wt), ?_⟩
  have hX : ∀ i : σ, (AlgHom.id O (MvPowerSeries σ O)) (MvPowerSeries.X i) ∈ maximalIdeal (MvPowerSeries σ O) := by
    intro i
    rw [AlgHom.id_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hord : ((N : ℕ) : ℕ∞) ≤ (f - ∑ j ∈ D.image (Finsupp.weight wt), wcomp O wt j f).order := by
    apply MvPowerSeries.nat_le_order
    intro d hd

    rw [map_sub, map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq, ite_eq_left, sub_self]
    exact Finset.mem_image_of_mem _ (by simpa [hD] using hd)
  have key := GlobalTheory.algHom_mem_pow_of_le_order (AlgHom.id O (MvPowerSeries σ O)) hX hord
  simpa using key

theorem UpperTheory.V.Alg.ker_gen :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] (σ : Type) [Finite σ] (wt : σ → X) (J : Ideal (MvPowerSeries σ O)), IsHomog O wt J →
      ∃ (n : ℕ) (f : Fin n → MvPowerSeries σ O) (c : Fin n → X), (∀ i, f i ∈ wtPart O wt (c i)) ∧ J = Ideal.span (Set.range f) := by
  intro O _ _ _ _ X _ σ _ wt J hJ
  classical
  set G : Set (MvPowerSeries σ O) := {g | ∃ f ∈ J, ∃ j : X, g = wcomp O wt j f} with hG
  have hGJ : Ideal.span G ≤ J := by
    rw [Ideal.span_le]
    rintro g ⟨f, hf, j, rfl⟩
    exact hJ f hf j
  have hJG : J ≤ Ideal.span G := by
    intro f hf
    apply ker_gen_closed (Ideal.span G) f
    intro N
    obtain ⟨T, hT⟩ := ker_gen_approx wt f N
    exact ⟨_, Ideal.sum_mem _ (fun j _ => Ideal.subset_span ⟨f, hf, j, rfl⟩), hT⟩
  have hfg : (Submodule.span (MvPowerSeries σ O) G).FG := IsNoetherian.noetherian _
  obtain ⟨s, hsG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
  have hchoice : ∀ g : s, ∃ j : X, g.1 ∈ wtPart O wt j := by
    rintro ⟨g, hg⟩
    obtain ⟨f, _, j, rfl⟩ := hsG hg
    exact ⟨j, wcomp_mem O wt j f⟩
  choose c hc using hchoice
  refine ⟨s.card, fun i => (s.equivFin.symm i).1, fun i => c (s.equivFin.symm i), fun i => hc _, ?_⟩
  have hrange : Set.range (fun i => (s.equivFin.symm i).1) = (s : Set (MvPowerSeries σ O)) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hg
      exact ⟨s.equivFin ⟨g, hg⟩, by simp⟩
  rw [hrange]
  calc J = Ideal.span G := le_antisymm hJG hGJ
    _ = Ideal.span (s : Set (MvPowerSeries σ O)) := hspan
