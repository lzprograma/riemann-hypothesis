module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

section
@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section
namespace GlobalTheory.EulerAbs

theorem avg_const_one {H : Type} [Group H] : avg (fun _ : H => (1 : ℂ)) = 1 := by
  have hs : rStab (fun _ : H => (1 : ℂ)) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [hs, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := uniqueOfSubsingleton (QuotientGroup.mk 1)
  rw [finsum_unique]
  simp

theorem twTerm_one_eq_one {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G)
    (hθ : ∀ k ∈ K, θ k ∈ K) (hδ : δ ∈ K) (hc : cptPart (twCent θ δ) ≤ K) :
    twTerm θ K δ ((K : Set G).indicator 1) 1 = 1 := by
  have hT : cptPart (twCent θ δ) ≤ twCent θ δ := by
    unfold cptPart
    rw [Subgroup.closure_le]
    intro t ht; exact ht.1
  have hmap : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
    ext x; simp
  have hidx : ((twCent θ δ ⊓ K.map (MulAut.conj (1 : G)).toMonoidHom).relIndex (cptPart (twCent θ δ))) = 1 := by
    rw [hmap, Subgroup.relIndex_eq_one]
    exact le_inf hT hc
  have hf : (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((1 * (k : G))⁻¹ * δ * θ (1 * k))) = fun _ => 1 := by
    funext k
    rw [Set.indicator_of_mem]
    · rfl
    · simp only [one_mul, SetLike.mem_coe]
      exact K.mul_mem (K.mul_mem (K.inv_mem k.2) hδ) (hθ _ k.2)
  unfold twTerm
  rw [hidx, hf, avg_const_one]
  simp

end GlobalTheory.EulerAbs
end
end
end


@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct


