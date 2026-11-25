module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin.NrmBasic

section General

variable {G Γ : Type} [Group G] [Group Γ] (φ : Γ →* MulAut G) (s : Γ)

theorem nrmG_zero (δ : G) : nrmG φ s 0 δ = 1 := by
  simp [nrmG]

theorem nrmG_succ (l : ℕ) (δ : G) : nrmG φ s (l + 1) δ = nrmG φ s l δ * φ (s ^ l) δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem nrmG_twConj (l : ℕ) (δ y : G) :
    nrmG φ s l (y⁻¹ * δ * φ s y) = y⁻¹ * nrmG φ s l δ * φ (s ^ l) y := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, nrmG_succ, ih]
    have h1 : φ (s ^ l) (y⁻¹ * δ * φ s y) = (φ (s ^ l) y)⁻¹ * φ (s ^ l) δ * φ (s ^ (l + 1)) y := by
      rw [map_mul, map_mul, map_inv, pow_succ, map_mul, MulAut.mul_apply]
    rw [h1]
    group

theorem mul_map_nrmG (l : ℕ) (δ : G) :
    δ * φ s (nrmG φ s l δ) = nrmG φ s l δ * φ (s ^ l) δ := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, map_mul, ← mul_assoc, ih, pow_succ', map_mul, MulAut.mul_apply]

theorem nrmG_mul (l : ℕ) (δ ε : G) (h : ∀ i j : ℕ, Commute (φ (s ^ i) δ) (φ (s ^ j) ε)) :
    nrmG φ s l (δ * ε) = nrmG φ s l δ * nrmG φ s l ε := by
  induction l with
  | zero => simp [nrmG_zero]
  | succ l ih =>
    rw [nrmG_succ, nrmG_succ, nrmG_succ, ih, map_mul]
    have hc : Commute (nrmG φ s l ε) (φ (s ^ l) δ) := by
      unfold nrmG
      apply Commute.list_prod_left
      intro x hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      exact (h l i).symm
    rw [mul_assoc, mul_assoc, ← mul_assoc (nrmG φ s l ε), hc.eq, mul_assoc]

end General

section Fields

variable {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']

theorem pow_finrank_eq_one (s : F' ≃ₐ[F] F') : s ^ Module.finrank F F' = 1 := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  rw [← IsGalois.card_aut_eq_finrank]
  exact pow_card_eq_one'

theorem fixed_iff (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (x : F') :
    s x = x ↔ x ∈ Set.range (algebraMap F F') := by
  haveI : Finite F := Finite.of_injective _ (algebraMap F F').injective
  constructor
  · intro hx
    rw [← IntermediateField.mem_bot, ← IsGalois.fixedField_top, IntermediateField.mem_fixedField_iff]
    intro t _
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hs t)
    exact MulAction.mem_fixedBy_zpow (α := F') (g := s) hx k
  · rintro ⟨a, rfl⟩
    exact s.commutes a

end Fields

theorem main : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ n : ℕ, (∀ x : GL (Fin n) F', galAct F F' n s x = x ↔ ∃ y, incl F F' n y = x) ∧ Function.Injective (incl F F' n) ∧ (∀ δ y : GL (Fin n) F', nrm s (y⁻¹ * δ * galAct F F' n s y) = y⁻¹ * nrm s δ * y) ∧ (∀ δ : GL (Fin n) F', δ * galAct F F' n s (nrm s δ) = nrm s δ * δ) ∧ ∀ δ ε : GL (Fin n) F', (∀ t u : F' ≃ₐ[F] F', Commute (galAct F F' n t δ) (galAct F F' n u ε)) → nrm s (δ * ε) = nrm s δ * nrm s ε := by
  intro F F' _ _ _ _ s hs n
  have hl := pow_finrank_eq_one s
  have hinj : Function.Injective (algebraMap F F') := (algebraMap F F').injective
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have he : ∀ i j, s ((x : Matrix (Fin n) (Fin n) F') i j) = (x : Matrix (Fin n) (Fin n) F') i j := by
        intro i j
        have := congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hx
        simpa [galAct_apply, gal] using this
      choose M0 hM using fun i j => (fixed_iff s hs _).1 (he i j)
      let M : Matrix (Fin n) (Fin n) F := Matrix.of M0
      have hdet : (algebraMap F F') (M.det) = (x : Matrix (Fin n) (Fin n) F').det := by
        rw [RingHom.map_det]
        congr 1
        ext i j
        exact hM i j
      have hu : IsUnit M := by
        rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
        intro h0
        have : (x : Matrix (Fin n) (Fin n) F').det = 0 := by rw [← hdet, h0, map_zero]
        exact (Matrix.GeneralLinearGroup.det_ne_zero x) this
      refine ⟨hu.unit, ?_⟩
      ext i j
      simp [incl, gal, M, hM]
    · rintro ⟨y, rfl⟩
      ext i j
      simp [galAct_apply, gal, incl]
  · intro a b hab
    ext i j
    have := congrArg (fun z : GL (Fin n) F' => (z : Matrix (Fin n) (Fin n) F') i j) hab
    exact hinj (by simpa [incl, gal] using this)
  · intro δ y
    unfold nrm
    rw [nrmG_twConj, hl, map_one, MulAut.one_apply]
  · intro δ
    unfold nrm
    rw [mul_map_nrmG, hl, map_one, MulAut.one_apply]
  · intro δ ε h
    unfold nrm
    exact nrmG_mul _ _ _ _ _ fun i j => h _ _

end GlobalTheory.Shin.NrmBasic

end
