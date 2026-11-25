module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

open Module

namespace GlobalTheory

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_isCompl_of_projective_quotient (N : Submodule R M) [Module.Projective R (M ⧸ N)] :
    ∃ N' : Submodule R M, IsCompl N N' := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' (y : M ⧸ N) : N.mkQ (s y) = y := LinearMap.congr_fun hs y
  refine ⟨LinearMap.range s, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    have hy : y = 0 := by
      rw [← hs' y, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hx
    rw [hy, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.2 ⟨x - s (N.mkQ x), ?_, s (N.mkQ x), ⟨_, rfl⟩, sub_add_cancel _ _⟩
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, hs', sub_self]

theorem finite_of_isCompl [Module.Finite R M] {N N' : Submodule R M} (h : IsCompl N N') :
    Module.Finite R N :=
  Module.Finite.equiv (Submodule.quotientEquivOfIsCompl N' N h.symm)

end General

section Valuation

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {M : Type*} [AddCommGroup M] [Module R M]


variable (R M) in
theorem free_of_finite_of_isTorsionFree_of_valuationRing [Module.Finite R M]
    [Module.IsTorsionFree R M] : Module.Free R M :=
  haveI : Module.Flat R M := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 ‹_›)
  Module.free_of_flat_of_isLocalRing

theorem IsSaturatedSubmodule.free_quotient_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R (M ⧸ N) :=
  haveI := h.isTorsionFree_quotient
  free_of_finite_of_isTorsionFree_of_valuationRing (R := R) (M := M ⧸ N)

theorem IsSaturatedSubmodule.exists_isCompl_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : ∃ N' : Submodule R M, IsCompl N N' :=
  haveI := h.free_quotient_of_valuationRing
  exists_isCompl_of_projective_quotient N

theorem IsSaturatedSubmodule.finite_of_valuationRing [Module.Finite R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Finite R N :=
  let ⟨_, h'⟩ := h.exists_isCompl_of_valuationRing
  finite_of_isCompl h'

theorem IsSaturatedSubmodule.free_of_valuationRing [Module.Finite R M] [Module.IsTorsionFree R M]
    {N : Submodule R M} (h : IsSaturatedSubmodule N) : Module.Free R N :=
  haveI := h.finite_of_valuationRing
  free_of_finite_of_isTorsionFree_of_valuationRing (R := R) (M := N)

end Valuation

universe u

end GlobalTheory
