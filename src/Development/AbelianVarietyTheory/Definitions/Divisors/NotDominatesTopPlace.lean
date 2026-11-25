module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
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

@[expose] public section

noncomputable section

namespace GlobalTheory.FieldPair

variable {k K L : Type} [Field k] [Field K] [Field L]

def NonUnit (R : Subring K) (f : K) : Prop := f ∈ R ∧ (f = 0 ∨ f⁻¹ ∉ R)

def RatRes (c : k →+* K) (R : Subring K) : Prop := ∀ r ∈ R, ∃ a, NonUnit R (r - c a)

def Dominates (ρ : K →+* L) (B : Subring L) (O : Subring K) : Prop :=
  ∀ f ∈ O, ρ f ∈ B ∧ (NonUnit O f → NonUnit B (ρ f))

structure IsEtTower (cK : k →+* K) (R : Subring K) (cL : k →+* L) (T : Subring L) {r : ℕ}
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) : Prop where

  base : IsLocModel cK R

  normal : IsIntegrallyClosed R

  top : IsLocModel cL T

  const : ∀ a, (ι ⟨cK a, base.const_mem a⟩ : L) = cL a

  retr : ∀ a, ψ (ι a) = a

  zero : ∀ i, ψ (τ i) = 0

  etale : (MvPolynomial.eval₂Hom ι τ).FormallyEtale


variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.nonUnit_iff {R : Subring K} (f : R) :
    _root_.GlobalTheory.FieldPair.NonUnit R f ↔ ¬ IsUnit f := by
  constructor
  · rintro ⟨-, h0 | hinv⟩ hu
    · have hf : f = 0 := Subtype.ext (by simpa using h0)
      exact not_isUnit_zero (hf ▸ hu)
    · obtain ⟨u, rfl⟩ := hu
      have hmul : ((u : R) : K) * ((u⁻¹ : Rˣ) : R) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]
        rfl
      rw [inv_eq_of_mul_eq_one_right hmul] at hinv
      exact hinv (u⁻¹ : Rˣ).1.2
  · intro hnu
    refine ⟨f.2, ?_⟩
    by_contra! h
    apply hnu
    exact IsUnit.of_mul_eq_one (b := (⟨_, h.2⟩ : R)) (Subtype.ext (by simp [h.1]))


variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.nonUnit_zero (R : Subring K) : _root_.GlobalTheory.FieldPair.NonUnit R 0 :=
  ⟨R.zero_mem, Or.inl rfl⟩


variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.not_nonUnit_one (R : Subring K) : ¬ _root_.GlobalTheory.FieldPair.NonUnit R 1 := by
  rintro ⟨-, h | h⟩
  · exact one_ne_zero h
  · exact h (by rw [inv_one]; exact R.one_mem)


variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.Dominates.trans {M : Type} [Field M] {ρ : K →+* L} {σ : L →+* M}
    {O : Subring K} {B : Subring L} {C : Subring M} (h : _root_.GlobalTheory.FieldPair.Dominates ρ B O)
    (h' : _root_.GlobalTheory.FieldPair.Dominates σ C B) :
    _root_.GlobalTheory.FieldPair.Dominates (σ.comp ρ) C O := by
  intro f hf
  obtain ⟨h1, h2⟩ := h f hf
  obtain ⟨h3, h4⟩ := h' (ρ f) h1
  exact ⟨h3, fun hn => h4 (h2 hn)⟩


variable {k K L : Type} [Field k] [Field K] [Field L] in
theorem _root_.GlobalTheory.FieldPair.ratRes_self : _root_.GlobalTheory.FieldPair.RatRes (RingHom.id k) ⊤ := by
  intro r _
  exact ⟨r, by rw [RingHom.id_apply, sub_self]; exact _root_.GlobalTheory.FieldPair.nonUnit_zero ⊤⟩

end GlobalTheory.FieldPair
