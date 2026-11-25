module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Plain
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def nfBasis (ϖ : kˣ) (g : GL n k) (e : Fin c → ℤ) (z : n → k) : GL (n ⊕ Fin c) k :=
  colE c 1 z * embX c g * embA n (SplitFlip.diagGL fun i => ϖ ^ e i)

theorem nfBasis_val (ϖ : kˣ) (g : GL n k) (e : Fin c → ℤ) (z : n → k) : (nfBasis ϖ g e z).val =
    fromBlocks g.val (Matrix.of fun r i => if i.val = 0 then z r * (ϖ : k) ^ e i else 0) 0
      (diagonal fun i => (ϖ : k) ^ e i) := by
  change fromBlocks 1 _ 0 1 * fromBlocks g.val 0 0 1 * fromBlocks 1 0 0 (diagonal _) = _
  rw [fromBlocks_multiply, fromBlocks_multiply]
  ext (r | r) (i | i) <;> simp

theorem nfBasis_one (ϖ : kˣ) (e : Fin c → ℤ) (z : n → k) : nfBasis ϖ 1 e z = normalBasis ϖ e z := by
  simp [nfBasis, normalBasis]

variable [ValuativeRel k]

def powInt (ϖ : kˣ) (e : ℤ) : Set k := {s | valuation k s ≤ valuation k ((ϖ ^ e : kˣ) : k)}

def topCoord (Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : Fin c) : Set k :=
  {s | ∃ y ∈ Λ, (∀ l, i < l → y (Sum.inr l) = 0) ∧ y (Sum.inr i) = s}

def MeetsIn (Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (L : Submodule 𝒪[k] (n → k)) : Prop :=
  ∀ y : n → k, Sum.elim y 0 ∈ Λ ↔ y ∈ L

def MapsLat {ι ι' : Type*} [Fintype ι'] (x : Matrix ι ι' k) (Λ' : Submodule 𝒪[k] (ι' → k))
    (Λ : Submodule 𝒪[k] (ι → k)) : Prop := ∀ v ∈ Λ', x *ᵥ v ∈ Λ

end Plain

variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def NormalFormModN : Prop :=
  ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (h : GL (n ⊕ Fin c) k),
    ∃ u ∈ N k n c 1, ∃ (g : GL n k) (e : Fin c → ℤ) (z : n → k),
      latOf (u * h) = latOf (nfBasis ϖ g e z) ∧ MeetsIn (latOf h) (latOf g)

variable [MeasurableSpace k] [BorelSpace k]

variable {k}
variable {s : ℕ} {X : ℕ → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type*} [Fintype Z] [DecidableEq Z]
  (T : Chain k s X Z) (ϖ : kˣ) (ψ : AddChar k Circle) (ν : Measure k)

def IsNormalRep (j c : ℕ) (h : j + c = s) (g : GL (X j ⊕ Fin (c + 1)) k) : Prop :=
  ∃ (e : Fin (c + 1) → ℤ) (z : X j → k), (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (∀ i, z i ∈ 𝒪[k]) ∧
    latOf (g * T.bas j (c + 1) (by omega)) = latOf (normalBasis ϖ e z)

def LastSteps : Prop :=
  ∀ A, T.IsRepSystem A ψ ν → T.RepsMeet A →
    (∀ g ∈ A s 0 rfl, IsNormalRep T ϖ s 0 rfl g) ∧
    (∀ g ∈ A s 0 rfl, ∀ x₀ y, T.Psi g x₀ y ≠ 0 → ∀ i, y i ∈ 𝒪[k]) ∧
    (∀ M : ℕ, 1 ≤ M → ∀ yb ∈ T.coupIdx A (box _ (ϖ ^ M)⁻¹) (box _ (ϖ ^ M)),
      ∀ y, Submodule.Quotient.mk y = yb → ∀ i, y i ∈ 𝒪[k]) ∧
    T.Adapted A (box _ (ϖ ^ (s + 1))⁻¹) (box _ (ϖ ^ (s + 1))) ∧
    ∀ ε : k, valuation k ε = 1 → ∀ yb ∈ T.coupIdx A (box _ (ϖ ^ (s + 1))⁻¹) (box _ (ϖ ^ (s + 1))),
      ∀ η, hat ψ ν ε (cosetInd _ yb) η ≠ 0 →
        ∀ y, Submodule.Quotient.mk y = yb → ε * (η ⬝ᵥ y) ∈ powInt ϖ (-((s : ℤ) + 1))



end GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
