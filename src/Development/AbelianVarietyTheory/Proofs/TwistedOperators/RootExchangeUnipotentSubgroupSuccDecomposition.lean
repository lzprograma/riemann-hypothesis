module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.RadicalDecomp
open GlobalTheory.RootEx.Radical

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem mem_N_of_succ {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c (p + 1))
    (h0 : ∀ (l : Fin c) (s : n), l.val + 1 = p → g.val (Sum.inr l) (Sum.inl s) = 0) :
    g ∈ N k n c p := by
  rw [mem_N_iff] at hg ⊢
  intro r s hrs
  rcases r with a | l <;> rcases s with b | j
  · exact hg _ _ (by simp [lev])
  · exact hg _ _ (by simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢; omega)
  · simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
    by_cases hp : l.val + 1 = p
    · rw [h0 l b hp]
      simp
    · exact hg _ _ (by simp only [lev, Sum.elim_inl, Sum.elim_inr]; omega)
  · exact hg _ _ (by simpa [lev] using hrs)

theorem inv_rowE_val (u : n → k) : ((rowE c p u)⁻¹).val =
    fromBlocks 1 0 (-(Matrix.of fun (l : Fin c) s => if l.val + 1 = p then u s else 0)) 1 := rfl

theorem succ_decomp : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), ∀ g ∈ N k n c (p + 1), ∃ g₁ ∈ N k n c p ⊓ N k n c (p + 1), ∃ u : n → k, g = g₁ * rowE c p u := by
  intro k _ n _ _ c p g hg
  set u : n → k := fun s => ∑ l : Fin c, if l.val + 1 = p then g.val (Sum.inr l) (Sum.inl s) else 0
    with hu
  have hE : rowE c p u ∈ N k n c (p + 1) := rowE_mem u (Nat.lt_succ_self p)
  have h1 : g * (rowE c p u)⁻¹ ∈ N k n c (p + 1) := Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hE)
  refine ⟨g * (rowE c p u)⁻¹, ⟨?_, h1⟩, u, by simp⟩
  refine mem_N_of_succ h1 ?_
  intro l s hl
  have hg' := (mem_N_iff g).1 hg
  have key : ∀ l' : Fin c, (l'.val + 1 = p ↔ l' = l) :=
    fun l' => ⟨fun h => Fin.ext (by omega), fun h => h ▸ hl⟩
  have hd : g.val (Sum.inr l) (Sum.inr l) = 1 := by
    have := hg' (Sum.inr l) (Sum.inr l) le_rfl
    simpa using this
  have hus : u s = g.val (Sum.inr l) (Sum.inl s) := by
    simp only [hu, key, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Units.val_mul, inv_rowE_val, Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [fromBlocks_apply₁₁, fromBlocks_apply₂₁, Matrix.one_apply, Matrix.neg_apply,
    Matrix.of_apply, key, mul_ite, mul_one, mul_zero, mul_neg, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, hus]
  simp only [Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hd]
  ring

end GlobalTheory.RootEx.RadicalDecomp
