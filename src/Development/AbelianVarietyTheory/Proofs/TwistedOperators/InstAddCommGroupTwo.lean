module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL

namespace GlobalTheory.SmGL.Exponents

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def leviChar {R β : Type} [CommRing R] [Fintype β] (c : β → Type) [∀ j, Fintype (c j)]
    [∀ j, DecidableEq (c j)] (χ : β → Rˣ →* ℂˣ) : Levi R c →* ℂˣ :=
  ∏ j, (detChar (c j) (χ j)).comp (Pi.evalMonoidHom (fun j => GL (c j) R) j)

theorem leviChar_apply {R β : Type} [CommRing R] [Fintype β] (c : β → Type) [∀ j, Fintype (c j)]
    [∀ j, DecidableEq (c j)] (χ : β → Rˣ →* ℂˣ) (g : Levi R c) :
    leviChar c χ g = ∏ j, χ j (Matrix.GeneralLinearGroup.det (g j)) := by
  simp [leviChar]

def wordMult {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (w : List ℂˣ) : ℕ∞ :=
  if w.length = n then jhMult (ofChar (torusChar fun i : Fin n => unrChar k (w.getD i 1))) (jacB π)
  else 0

theorem wordMult_ofFn {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) (z : Fin n → ℂˣ) :
    wordMult π (List.ofFn z) = jhMult (ofChar (torusChar fun i => unrChar k (z i))) (jacB π) := by
  simp [wordMult]

theorem wordMult_of_ne {n : ℕ} (π : Representation ℂ (GL (Fin n) k) V) {w : List ℂˣ}
    (h : w.length ≠ n) : wordMult π w = 0 := by
  rw [wordMult, ite_eq_right h]

def jacEquiv {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W} (φ : π.Equiv τ) :
    (jac e π).Equiv (jac e τ) :=
  LocGL.equivOfBijective (jacMap e φ.toIntertwiningMap) (Function.bijective_iff_has_inverse.2
    ⟨jacMap e φ.symm.toIntertwiningMap, fun x => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact congrArg Submodule.Quotient.mk (φ.symm_apply_apply v), fun x => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact congrArg Submodule.Quotient.mk (φ.apply_symm_apply v)⟩)

theorem wordMult_congr {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V}
    {τ : Representation ℂ (GL (Fin n) k) W} (φ : π.Equiv τ) (w : List ℂˣ) :
    wordMult π w = wordMult τ w := by
  unfold wordMult
  split_ifs
  · exact jhMult_congr_right _ (Representation.Equiv.mk (jacEquiv (points (Fin n)) φ).toLinearEquiv
      fun t => (jacEquiv (points (Fin n)) φ).isIntertwining' _)
  · rfl

instance instAddCommGroupTwo : ∀ x, AddCommGroup (Two V W x)
  | false => inferInstanceAs (AddCommGroup V)
  | true => inferInstanceAs (AddCommGroup W)

instance instModuleTwo : ∀ x, Module ℂ (Two V W x)
  | false => inferInstanceAs (Module ℂ V)
  | true => inferInstanceAs (Module ℂ W)

def twoRep {R a b : Type} [CommRing R] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (π₁ : Representation ℂ (GL a R) V) (π₂ : Representation ℂ (GL b R) W) :
    ∀ x, Representation ℂ (GL (Two a b x) R) (Two V W x)
  | false => π₁
  | true => π₂

end GlobalTheory.SmGL.Exponents
