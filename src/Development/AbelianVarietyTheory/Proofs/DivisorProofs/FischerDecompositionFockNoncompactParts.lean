module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineKroneckerRightMatrixConjTranspose
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.JointHarm

namespace GlobalTheory.FischerParts

theorem exists_fockIP (σ : Type) [DecidableEq σ] :
    ∃ ι : MvPolynomial σ ℂ →ₗ[ℂ] lp (fun _ : σ →₀ ℕ => ℂ) 2,
      IsFockIP ι ∧ Function.Injective ι := by
  classical
  let w : (σ →₀ ℕ) → ℕ := fun α => α.prod fun _ k => k.factorial
  have hw : ∀ α, w α ≠ 0 := fun α => Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  let v : (σ →₀ ℕ) → lp (fun _ : σ →₀ ℕ => ℂ) 2 := fun α => lp.single 2 α (√(w α) : ℝ)
  have hv : ∀ α β, inner ℂ (v α) (v β) = if α = β then (w α : ℂ) else 0 := by
    intro α β
    simp only [v, lp.inner_single_left, lp.single_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      simp only [RCLike.inner_apply, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    · simp
  refine ⟨(basisMonomials σ ℂ).constr ℂ v, fun α β => ?_, ?_⟩
  · have e : ∀ α, (basisMonomials σ ℂ).constr ℂ v (monomial α 1) = v α := fun α => by
      have := (basisMonomials σ ℂ).constr_basis ℂ v α
      rwa [coe_basisMonomials] at this
    rw [e, e, hv]
    simp [w, Finsupp.prod]
  · refine (basisMonomials σ ℂ).injective_constr_of_linearIndependent ?_
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun α h => hw α ?_) fun α β h => ?_
    · have := hv α α
      rw [h, inner_zero_left, ite_eq_left rfl] at this
      exact_mod_cast this.symm
    · exact (hv α β).trans (ite_eq_right h)

theorem fischer_parts : ∀ (p q r s d : ℕ), (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm2 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm1 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (jointHarm p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨ ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) := by
  intro p q r s d
  obtain ⟨ι, hι, hinj⟩ := exists_fockIP (Ln p q r s)
  refine ⟨fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron1 r s Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron2 p q Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | (∃ Z, IsPC Z ∧ M = kron1 r s Z) ∨ ∃ Z, IsPC Z ∧ M = kron2 p q Z}
      ?_ ?_ d _ _ (fun P hP => ?_) fun P => ?_⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron1 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron2 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [odd_kron1 hZ, odd_kron2 hZ]
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [⟨_, .inl ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩,
      ⟨_, .inr ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩]
  · exact ⟨fun Z hZ => hP _ (.inl ⟨Z, hZ, rfl⟩), fun Z hZ => hP _ (.inr ⟨Z, hZ, rfl⟩)⟩
  · constructor
    · rintro ⟨Q, hQ, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩⟩
      exacts [⟨Q, hQ, _, .inl ⟨Z, hZ, rfl⟩, rfl⟩, ⟨Q, hQ, _, .inr ⟨Z, hZ, rfl⟩, rfl⟩]
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩, rfl⟩
      exacts [⟨Q, hQ, .inl ⟨Z, hZ, rfl⟩⟩, ⟨Q, hQ, .inr ⟨Z, hZ, rfl⟩⟩]

end GlobalTheory.FischerParts
