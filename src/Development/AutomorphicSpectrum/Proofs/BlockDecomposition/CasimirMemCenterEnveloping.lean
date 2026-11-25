module

public import Formalism.RealPlaceAnalysis.StatementA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QdetTopThreeOrders
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnveloping

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec", "h": "module\n\nimport Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue\npublic import Formalism.RealPlaceAnalysis.StatementA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Monotonicity.Lemmas\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Presheaf\n\n"}
section -- clump:auto
@[expose] public section

open Finset

namespace GlobalTheory.CompanionTheory.Inh.CapelliCasimir
open Polynomial

noncomputable def rev {ι : Type} (s : Finset ι) (f : ι → ℂ) : ℂ[X] := ∏ l ∈ s, (1 + C (f l) * X)

theorem scalar_core (n : ℕ) (hn : 2 ≤ n) (ρ μ a : Fin n → ℂ) (b : Fin n → Fin n → ℂ) (r : ℕ → ℂ)
    (e c : ℂ)
    (h : ∀ Y : ℂ, (∏ l, (Y + ρ l)) * e + ∑ i, (∏ l ∈ univ.erase i, (Y + ρ l)) * a i
      + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (∏ l ∈ (univ.erase i).erase j, (Y + ρ l)) * b i j
      + ∑ d ∈ range (n - 2), (Y + c) ^ d * r d = (∏ l, (Y + μ l)) * e) :
    (∑ l, ρ l) * e + ∑ i, a i = (∑ l, μ l) * e ∧
    ((∑ l, ρ l) ^ 2 - ∑ l, ρ l ^ 2) * e + 2 * ∑ i, (∑ l ∈ univ.erase i, ρ l) * a i
      + 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), b i j
      = ((∑ l, μ l) ^ 2 - ∑ l, μ l ^ 2) * e := by
  apply GlobalTheory.CapelliCasimir.scalar_core <;> assumption


end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnveloping =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnveloping", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin\npublic import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QdetTopThreeOrders\npublic import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum\nimport GroundTheory.AutomorphicForms.ReductionBlock\nimport GroundTheory.GlobalFields.KummerTheory.LocalIndex\nimport Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.Inh.CapelliCasimir
open Finset

theorem mem_subalgebra_of_dual {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (x : A)
    (h : ∀ f : A →ₗ[ℂ] ℂ, (∀ z ∈ S, f z = 0) → f x = 0) : x ∈ S := by
  by_contra hx
  have hx' : x ∉ Subalgebra.toSubmodule S := hx
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem hx'
  exact hf1 (h f fun z hz => LinearMap.mem_ker.1 (hf2 hz))

theorem cas_mem_of_qdet_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (n : ℕ)
    (E : Fin n → Fin n → A) (hE : Formalism.REAL.GlRel E)
    (hcap : ∀ Y : ℂ, Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) ∈ S) : Formalism.REAL.Cas E ∈ S := by
  obtain ⟨Rm, hR⟩ := _root_.GlobalTheory.qdet_top_three_orders A n E
  by_cases hn : 2 ≤ n
  swap
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · simp [Formalism.REAL.Cas]
    · have h0 := hcap 0
      rw [hR] at h0
      have h1 : E 0 0 ∈ S := by
        simpa [Finset.filter_singleton] using h0
      have : Formalism.REAL.Cas E = E 0 0 * E 0 0 := by simp [Formalism.REAL.Cas]
      rw [this]
      exact Subalgebra.mul_mem _ h1 h1
  set ρ : Fin n → ℂ := fun l => ((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ) with hρ
  have hρ0 : ∑ l, ρ l = 0 := by
    have h1 : ∑ l, ρ l = ∑ l, ρ (Fin.rev l) := (Equiv.sum_comp Fin.revPerm ρ).symm
    have h2 : ∑ l, ρ (Fin.rev l) = - ∑ l, ρ l := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      have := l.2
      simp only [hρ, Fin.val_rev]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linear_combination (h1.trans h2) / 2
  have core := fun (f : A →ₗ[ℂ] ℂ) (hf : ∀ z ∈ S, f z = 0) =>
    scalar_core n hn ρ (fun _ => 0) (fun i => f (E i i))
      (fun i j => f (E i i * E j j - E j i * E i j)) (fun d => f (Rm d)) (f 1)
      (((n : ℂ) - 1) / 2)
      (fun Y => by
        have h1 := hf _ (hcap Y)
        rw [hR] at h1
        have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)

        simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, add_sub_assoc] at h1
        simp only [e, mul_zero] at h1 ⊢
        exact h1)
  have hT : ∑ i, E i i ∈ S := by
    refine mem_subalgebra_of_dual S _ fun f hf => ?_
    have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
    have := (core f hf).1
    rw [hρ0, e] at this

    simp only [map_sum]
    linear_combination this
  have hW : (2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i ∈ S := by
    refine mem_subalgebra_of_dual S _ fun f hf => ?_
    have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
    have h2 := (core f hf).2
    rw [e] at h2
    simp only [sum_erase_eq_sub (mem_univ _), hρ0] at h2

    simp only [map_sub f, map_sum, map_smul, smul_eq_mul]
    have h5 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) * f (E i i)
        = - (2 * ∑ i, (0 - ρ i) * f (E i i)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [hρ]; ring
    rw [h5]
    simp only [map_sub f] at h2
    linear_combination h2
  have h3 := GlobalTheory.CapelliCasimir.sq_sub_cas E hE
  have : Formalism.REAL.Cas E = (∑ i, E i i) * (∑ i, E i i)
      - ((2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i) := by
    rw [← h3]; abel
  rw [this]
  exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hT hT) hW

theorem cas_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  intro F _ _ _ n τ
  have hcap : ∀ Y : ℂ, cap (a := n) τ Y ∈ Zalg F n := fun Y =>
    Algebra.subset_adjoin (show cap (a := n) τ Y ∈ {z | ∃ τ u, z = cap τ u} from ⟨τ, Y, rfl⟩)
  exact cas_mem_of_qdet_mem (Zalg F n) n (Eop τ) (glRel_Eop τ) hcap

end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnveloping =====
