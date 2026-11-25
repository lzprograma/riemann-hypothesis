module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.UnitaryDetClass
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GlobalTheory.PushHarm

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n : ℕ}

theorem push_X (γ : Matrix (Fin n) (Fin n) E) (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (j : Fin n) :
    push c γ (X (⟨σ, i, j⟩ : LtN Dw n)) =
      ∑ k, C (embF c σ (γ k j)) * X (⟨σ, i, k⟩ : LtN Dw n) := by
  simp [push, letB]

open Classical in
theorem pderiv_push_X (γ : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (a : Fin (Dw.mult τ)) (b : Fin n)
    (ℓ : LtN Dw n) :
    pderiv (⟨τ, a, b⟩ : LtN Dw n) (push c γ (X ℓ)) =
      ∑ j, embF c τ (γ b j) • push c γ (pderiv (⟨τ, a, j⟩ : LtN Dw n) (X ℓ)) := by
  obtain ⟨σ, i, j⟩ := ℓ

  rw [push_X, map_sum]
  simp only [pderiv_C_mul, pderiv_X]
  by_cases hσ : σ = τ
  · subst hσ
    by_cases hi : i = a
    · subst hi
      rw [Finset.sum_eq_single b, Finset.sum_eq_single j]
      · simp [smul_eq_C_mul]
      · intro k _ hk
        rw [Pi.single_eq_of_ne]
        · simp
        · simpa using hk.symm
      · simp
      · intro k _ hk
        rw [Pi.single_eq_of_ne]
        · simp
        · simpa using hk
      · simp
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · intro k _
        rw [Pi.single_eq_of_ne]
        · simp
        · simp [hi]
      · intro k _
        rw [Pi.single_eq_of_ne]
        · simp
        · simp [hi]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro k _
      rw [Pi.single_eq_of_ne]
      · simp
      · exact fun h => hσ (congrArg Sigma.fst h)
    · intro k _
      rw [Pi.single_eq_of_ne]
      · simp
      · exact fun h => hσ (congrArg Sigma.fst h)

theorem pderiv_push (γ : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (a : Fin (Dw.mult τ)) (b : Fin n)
    (P : MvPolynomial (LtN Dw n) c.F) :
    pderiv (⟨τ, a, b⟩ : LtN Dw n) (push c γ P) =
      ∑ j, embF c τ (γ b j) • push c γ (pderiv (⟨τ, a, j⟩ : LtN Dw n) P) := by
  induction P using MvPolynomial.induction_on with
  | C x => simp [push]
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib]
  | mul_X p ℓ hp =>
    rw [map_mul, Derivation.leibniz, hp, pderiv_push_X]
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, smul_add, Finset.sum_add_distrib,
      Finset.mul_sum, mul_smul_comm]

theorem lap_one_apply {T : Type} {r : T → ℕ} {k : Type} [Field k] (τ τ' : T) (a : Fin (r τ))
    (a' : Fin (r τ')) (P : MvPolynomial (Letter T r n) k) :
    lap r n k 1 τ τ' a a' P =
      ∑ b, pderiv (⟨τ, a, b⟩ : Letter T r n) (pderiv (⟨τ', a', b⟩ : Letter T r n) P) := by
  simp [lap, Matrix.one_apply, LinearMap.sum_apply, ite_smul]

theorem lap_push (γ : Matrix (Fin n) (Fin n) E) (hγ : IsUnitary γ) (τ : E →+* ℂ) (a : Fin (Dw.mult τ))
    (a' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))) (P : MvPolynomial (LtN Dw n) c.F) :
    lap Dw.mult n c.F 1 τ (ComplexEmbedding.conjugate τ) a a' (push c γ P) =
      push c γ (lap Dw.mult n c.F 1 τ (ComplexEmbedding.conjugate τ) a a' P) := by
  have hc : ∀ x : E, embF c (ComplexEmbedding.conjugate τ) x = embF c τ (IsCMField.complexConj E x) :=
    fun x => Subtype.ext (IsCMField.complexEmbedding_complexConj E τ x).symm
  have hu : ∀ j' j : Fin n, ∑ b, embF c (ComplexEmbedding.conjugate τ) (γ b j') * embF c τ (γ b j) =
      if j' = j then 1 else 0 := by
    intro j' j
    have h := congrArg (embF c τ) (congrFun (congrFun hγ j') j)

    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    Matrix.one_apply, apply_ite (embF c τ), map_one, map_zero] at h
    simpa only [hc] using h

  rw [lap_one_apply, lap_one_apply, map_sum]

  simp only [pderiv_push, map_sum, Derivation.map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hu, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

theorem push_mem_harmK : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (c : Coeff l) (n : ℕ) (γ : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.IsUnitary γ →
    P ∈ harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass.push (Dw := Dw) c γ P ∈
      harmK Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun _ => 1) := by
  intro E _ _ _ H Dw l c n γ P hγ hP
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at hP ⊢
  intro τ hτ a a'
  rw [lap_push c γ hγ, hP τ hτ a a', map_zero]

end GlobalTheory.PushHarm
