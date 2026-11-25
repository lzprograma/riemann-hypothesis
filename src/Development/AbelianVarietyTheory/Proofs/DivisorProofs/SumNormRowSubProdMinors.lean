module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CBinet
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Classical

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

def smEquivSub (a d : ℕ) : {s : Fin a → Fin d // StrictMono s} ≃ {S : Finset (Fin d) // S.card = a} where
  toFun s := ⟨Finset.univ.map ⟨s.1, s.2.injective⟩, by simp⟩
  invFun S := ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩
  left_inv s := by
    apply Subtype.ext
    symm
    exact Finset.orderEmbOfFin_unique _ (fun x => by simp) s.2
  right_inv S := by
    apply Subtype.ext
    simp only
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨y, rfl⟩; exact Finset.orderEmbOfFin_mem _ _ _
    · intro hx
      have : x ∈ Set.range (S.1.orderEmbOfFin S.2) := by rw [Finset.range_orderEmbOfFin]; exact hx
      exact this

theorem det_mul_eq_sum_sm {R : Type} [CommRing R] {a d : ℕ} (A : Matrix (Fin a) (Fin d) R)
    (B : Matrix (Fin d) (Fin a) R) :
    (A * B).det = ∑ s : {s : Fin a → Fin d // StrictMono s},
      (A.submatrix id s.1).det * (B.submatrix s.1 id).det := by
  rw [ReciprocityTheory.ChartRestriction.DS.S7.det_mul_eq_sum_submatrix, ← (smEquivSub a d).symm.sum_comp]
  rfl

end GlobalTheory.MinorFrame

noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
open scoped Matrix
variable {ι : Type} [Fintype ι]

def xMat (τ : ι) (d a : ℕ) : Matrix (Fin d) (Fin a) (Pol ι d a) := Matrix.of fun i j => X (τ, i, j)

end GlobalTheory.MinorFrame

noncomputable section

noncomputable section

noncomputable section
