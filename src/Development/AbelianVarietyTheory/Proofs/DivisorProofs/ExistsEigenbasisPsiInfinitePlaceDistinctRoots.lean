module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableFormGroupElementFixesUniquePositiveLine
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDiagonalizableOfCharpolyEqProdDistinct
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
import GroundTheory.Brauer.TensorSimple
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRootsMapPol, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbasisPsiInfinitePlaceDistinctRoots

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRootsMapPol =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRootsMapPol", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem card_roots_map_minpoly {p : ℕ} [Fact p.Prime] (G : HTGroup p) (γ : G.C)
    (hreg : (minpoly G.F γ).natDegree = G.n ∧ (minpoly G.F γ).Separable) (φ : G.F →+* ℂ) :
    (((minpoly G.F γ).map φ).roots.toFinset).card = G.n ∧ (minpoly G.F γ).Monic := by
  have hint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hmon : (minpoly G.F γ).Monic := minpoly.monic hint
  refine ⟨?_, hmon⟩
  have hsep : ((minpoly G.F γ).map φ).Separable := hreg.2.map
  have hdeg : ((minpoly G.F γ).map φ).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hreg.1
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep), ← hdeg]
  exact IsAlgClosed.card_roots_eq_natDegree

end GlobalTheory.LKMid
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRootsMapPol =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbasisPsiInfinitePlaceDistinctRoots =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbasisPsiInfinitePlaceDistinctRoots", "h": "module\n\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyPsiEqMapMinpoly\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardRootsMapPol\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDiagonalizableOfCharpolyEqProdDistinct\nimport GroundTheory.Brauer.TensorSimple\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.LinearAlgebra.Matrix.FiniteDimensional\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

theorem psi_eigenbasis_of_regular (G : HTGroup p) (γ : G.C) (v : InfinitePlace G.F)
    (hreg : (minpoly G.F γ).natDegree = G.n ∧ (minpoly G.F γ).Separable) :
    ∃ (Z : GL (Fin G.n) ℂ) (lam : Fin G.n → ℂ), Function.Injective lam ∧
      (∀ z : ℂ, (minpoly G.F γ).eval₂ v.embedding z = 0 ↔ ∃ i, lam i = z) ∧
      G.psi v γ * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) =
        (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * Matrix.diagonal lam := by
  set Q := (minpoly G.F γ).map v.embedding with hQ
  obtain ⟨hcard, hmon⟩ := card_roots_map_minpoly G γ hreg v.embedding
  have hsep : Q.Separable := hreg.2.map
  have hnd : Q.roots.Nodup := Polynomial.nodup_roots hsep
  have hQm : Q.Monic := hmon.map _
  have hne : (minpoly G.F γ) ≠ 0 := hmon.ne_zero
  let e : Fin G.n ≃ {x // x ∈ Q.roots.toFinset} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hcard)).symm
  let lam : Fin G.n → ℂ := fun i => (e i : ℂ)
  have hlam : Function.Injective lam := fun i j h => e.injective (Subtype.ext h)
  have hprod : Q = ∏ k, (X - C (lam k)) := by
    have h1 : Q = (Q.roots.map (fun a => X - C a)).prod :=
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm
        (IsAlgClosed.card_roots_eq_natDegree)).symm
    rw [h1]
    have h2 : (Q.roots.map (fun a => X - C a)).prod = ∏ a ∈ Q.roots.toFinset, (X - C a) := by
      rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
    rw [h2, ← Finset.prod_coe_sort]
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  have hcp : (G.psi v γ).charpoly = ∏ k, (X - C (lam k)) := by
    rw [charpoly_psi_eq_map_minpoly G v γ hreg.1, ← hQ, ← hprod]
  obtain ⟨Z, hZ⟩ := GlobalTheory.matrix_diagonalizable_of_charpoly_eq_prod_distinct ℂ G.n _ lam hlam hcp
  refine ⟨Z, lam, hlam, fun z => ?_, hZ⟩
  rw [← Polynomial.mem_roots_map_of_injective v.embedding.injective hne, ← hQ, ← Multiset.mem_toFinset]
  constructor
  · intro hz
    exact ⟨e.symm ⟨z, hz⟩, by simp [lam]⟩
  · rintro ⟨i, rfl⟩
    exact (e i).2

end GlobalTheory.LKMid
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbasisPsiInfinitePlaceDistinctRoots =====
