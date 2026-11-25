module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PerfectPairingQuotients
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

@[expose] public section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil


open Classical in
open scoped BigOperators in
theorem _root_.GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul : ∀ {R X M : Type} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
    {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, _root_.GlobalTheory.FinWeil.IsHeis σ w γ W →
    ∀ (A B : Submodule R X), _root_.GlobalTheory.FinWeil.SelfDual γ A → _root_.GlobalTheory.FinWeil.SelfDual γ B →
    _root_.GlobalTheory.FinWeil.idx A B ≠ 0 →
    _root_.GlobalTheory.FinWeil.idx B A = _root_.GlobalTheory.FinWeil.idx A B ∧
      ∀ v, _root_.GlobalTheory.FinWeil.Fixes W A v →
        _root_.GlobalTheory.FinWeil.sumOp W B A (_root_.GlobalTheory.FinWeil.sumOp W A B v) =
          (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v := by
  intro R X M _ _ _ _ _ σ w γ W hW A B hA hB hAB
  obtain ⟨hidx, -, hsum⟩ := _root_.GlobalTheory.FinWeil.perfect_pairing_quotients hW B.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup B.toAddSubgroup (fun a _ => hB a)
    (fun t _ => (hA t).trans (forall₂_congr fun a _ =>
      ⟨hW.swap_eq_one, hW.swap_eq_one⟩)) hAB
  refine ⟨hidx, fun v hv => ?_⟩
  have hfinB : (A.toAddSubgroup.addSubgroupOf B.toAddSubgroup).FiniteIndex := ⟨hAB⟩
  have hfinA : (B.toAddSubgroup.addSubgroupOf A.toAddSubgroup).FiniteIndex := by
    refine ⟨?_⟩
    change B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0
    rw [hidx]; exact hAB
  letI := Fintype.ofFinite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup)
  letI := Fintype.ofFinite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup)
  unfold _root_.GlobalTheory.FinWeil.sumOp

  simp_rw [finsum_eq_sum_of_fintype, map_sum] at hsum ⊢
  have hcomm : ∀ a ∈ A, ∀ b : X, W a (W b v) = γ a b • W b v := by
    intro a ha b
    rw [hW.comm, hv a ha]
  calc ∑ q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup,
        ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          W (Quotient.out q).1 (W (Quotient.out p).1 v)
      = ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          (∑ q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup,
            γ (Quotient.out q).1 (Quotient.out p).1) • W (Quotient.out p).1 v := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun q _ => hcomm _ (Quotient.out q).2 _
    _ = ∑ p : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup,
          if p = 0 then (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v else 0 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hsum _ (Quotient.out p).2]
        have hmem : (Quotient.out p).1 ∈ A.toAddSubgroup ↔ p = 0 := by
          conv_rhs => rw [← QuotientAddGroup.out_eq' p]
          rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
        by_cases hp : p = 0
        · rw [ite_eq_left (hmem.2 hp), ite_eq_left hp, hv _ (hmem.2 hp)]
          exact congrArg (fun n : ℕ => (n : ℂ) • v) hidx
        · rw [ite_eq_right (mt hmem.1 hp), ite_eq_right hp, zero_smul]
    _ = (_root_.GlobalTheory.FinWeil.idx A B : ℂ) • v := by
        rw [Finset.sum_ite_eq']
        simp

end GlobalTheory.FinWeil
