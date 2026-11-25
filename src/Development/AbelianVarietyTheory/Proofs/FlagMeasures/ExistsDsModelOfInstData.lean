module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

@[expose] public section

open Formalism.MainNotions.ArithmeticCylinders IsDedekindDomain MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical

namespace GlobalTheory.RowLev

theorem isEnum_parA_zero (D : D7) {n : ℕ} (hn : n = D.R.r) (τ : D.what₂.Tau) :
    IsEnum (parA (tparRec D) 0 τ) (fun i : Fin n => lamS D.R (D.hc τ) (Fin.cast hn i))
      (fun i => epsS D.R (Fin.cast hn i)) := by
  subst hn
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  simp only [Fin.cast_eq_self]
  refine ⟨?_, fun i => if h : i.val < D.R.k - 1 then (D.hc τ).v ⟨i.val, h⟩
    else if h' : i.val - (D.R.k - 1) < D.R.m then -(D.hc τ).b ⟨i.val - (D.R.k - 1), h'⟩ else 0, ?_, ?_⟩
  · have h := (GlobalTheory.Mem.Vol.lamSH_isHCParam D.R (D.hc τ)).1
    intro a b hab
    have := h (a := Fin.cast (dimS_eq D.R).symm a) (b := Fin.cast (dimS_eq D.R).symm b) hab
    simpa [lamSH] using this
  · intro a
    simp only [lamS]
    split_ifs <;> simp
  · have hpar : ∀ a : ℕ, decide (a ≤ 0 ∨ Even (a - 0)) = decide (a % 2 = 0) := by
      intro a
      rw [decide_eq_decide, Nat.sub_zero, Nat.even_iff]
      omega
    ext x
    simp only [parA, TPar.Dpar, tparRec, tparHC, hpar, Nat.not_odd_zero, ite_false, add_zero,
      Nat.not_lt_zero, Finset.filter_false, Finset.biUnion_empty, Finset.union_empty, Prod.mk.eta,
      Finset.image_id', Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · refine ⟨⟨i.val, by have := i.2; omega⟩, ?_⟩
        simp [epsS, i.2]
      · refine ⟨⟨i.val + (D.R.k - 1), by have := i.2; omega⟩, ?_⟩
        simp [epsS, i.2]
    · rintro ⟨a, rfl⟩
      by_cases h : a.val < D.R.k - 1
      · exact Or.inl ⟨⟨a.val, h⟩, by simp [epsS, h]⟩
      · have h' : a.val - (D.R.k - 1) < D.R.m := by have := a.2; omega
        exact Or.inr ⟨⟨_, h'⟩, by simp [epsS, h, h']⟩

end GlobalTheory.RowLev
