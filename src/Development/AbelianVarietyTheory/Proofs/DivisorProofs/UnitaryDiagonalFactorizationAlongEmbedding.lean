module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
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

@[expose] public section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl


open Classical in
theorem emb_mul_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n r : ℕ}
    {e : Fin r → Fin n} {ι : GU σ r →* GU σ n} (he : Function.Injective e) (hι : IsEmb e ι)
    (D : Fin n → L) (s : GU σ r) (hs : mat s = Matrix.diagonal (D ∘ e)) :
    mat (ι s) * Matrix.diagonal (fun a => if a ∈ Set.range e then 1 else D a) = Matrix.diagonal D := by
  ext a b
  rw [Matrix.mul_diagonal]
  by_cases hb : b ∈ Set.range e
  · rw [ite_eq_left hb, mul_one]
    by_cases ha : a ∈ Set.range e
    · obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      rw [(hι s).1, hs]
      simp [Matrix.diagonal_apply, he.eq_iff]
    · have hab : a ≠ b := fun h => ha (h ▸ hb)
      rw [(hι s).2 a b (Or.inl ha), Matrix.one_apply_ne hab, Matrix.diagonal_apply_ne _ hab]
  · rw [ite_eq_right hb, (hι s).2 a b (Or.inr hb)]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.one_apply_ne hab, Matrix.diagonal_apply_ne _ hab, zero_mul]

theorem embTorus : EmbTorus := by
  classical
  intro L _ _ σ n r e ι he hι D D' t t' s s' ht ht' hs hs' hD
  have h1 := emb_mul_diagonal he hι D s hs
  have h2 := emb_mul_diagonal he hι D' s' hs'
  have hZ : (fun a => if a ∈ Set.range e then (1 : L) else D' a) =
      fun a => if a ∈ Set.range e then (1 : L) else D a := by
    funext a
    by_cases ha : a ∈ Set.range e
    · rw [ite_eq_left ha, ite_eq_left ha]
    · rw [ite_eq_right ha, ite_eq_right ha, hD a ha]
  have hz : mat ((ι s)⁻¹ * t) = Matrix.diagonal (fun a => if a ∈ Set.range e then (1 : L) else D a) := by
    rw [mat_mul, ht, ← h1, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  refine ⟨(ι s)⁻¹ * t, by group, ?_, fun g => ?_⟩
  · apply mat_injective
    rw [mat_mul, hz, ← hZ, ht', ← h2]
  · apply mat_injective
    rw [mat_mul, mat_mul (ι g), hz]
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hab : a = b
    · subst hab
      exact mul_comm _ _
    · by_cases ha : a ∈ Set.range e
      · by_cases hb : b ∈ Set.range e
        · rw [ite_eq_left ha, ite_eq_left hb, one_mul, mul_one]
        · rw [(hι g).2 a b (Or.inr hb), Matrix.one_apply_ne hab, mul_zero, zero_mul]
      · rw [(hι g).2 a b (Or.inl ha), Matrix.one_apply_ne hab, mul_zero, zero_mul]

end GlobalTheory.SatakeWeyl
