module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Perm.Sign
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.Reformulated.B.Qf10

noncomputable def GlRel.{u_1} : {A : Type u_1} → [Ring A] → {n : ℕ} → (Fin n → Fin n → A) → Prop := fun {A} [Ring A] {n} E =>
  ∀ (a b c d : Fin n), E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - if d = a then E c b else 0

noncomputable def Tm.{u_1} : {A : Type u_1} → [inst : Ring A] → [Algebra ℂ A] → {n : ℕ} → (Fin n → Fin n → A) → ℂ → Fin n → Fin n → A := fun {A} [Ring A] [Algebra ℂ A] {_} E u a b => (if a = b then (algebraMap ℂ A) u else 0) + E a b

noncomputable def qminor.{u_1} : {A : Type u_1} →
  [inst : Ring A] → [Algebra ℂ A] → {n t : ℕ} → (Fin n → Fin n → A) → (Fin t → Fin n) → (Fin t → Fin n) → ℂ → A := fun {A} [Ring A] [Algebra ℂ A] {_ _} E a b u =>
  ∑ σ, ↑↑(Equiv.Perm.sign σ) * (List.ofFn fun k => Tm E (u - ↑↑k) (a (σ k)) (b k)).prod

noncomputable def qdet {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : A :=
  qminor E (id : Fin n → Fin n) id u

theorem casimir : ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module ℂ V]
  (E : Fin 2 → Fin 2 → Module.End ℂ V),
  GlRel E →
    ∀ (k : ℂ) (φ : V),
      (E 0 0) φ + (E 1 1) φ = 0 →
        (E 0 1) φ - (E 1 0) φ = (Complex.I * k) • φ →
          (E 0 0) φ - (E 1 1) φ = Complex.I • ((E 0 1) φ + (E 1 0) φ) →
            ∀ (u : ℂ),
              (qdet E (u + 1 / 2)) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ := by
  intro V _ _ E hE k φ h1 h2 h3 u
  have rel : ∀ a b c d : Fin 2, E a b (E c d φ) - E c d (E a b φ) =
      (if b = c then E a d φ else 0) - (if d = a then E c b φ else 0) := by
    intro a b c d
    have h := congrArg (fun f : Module.End ℂ V => f φ) (hE a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    rw [h]
    split_ifs <;> simp
  have rab : E 0 0 (E 0 1 φ) - E 0 1 (E 0 0 φ) = E 0 1 φ := by simpa using rel 0 0 0 1
  have rac : E 0 0 (E 1 0 φ) - E 1 0 (E 0 0 φ) = -E 1 0 φ := by simpa using rel 0 0 1 0
  have rdb : E 1 1 (E 0 1 φ) - E 0 1 (E 1 1 φ) = -E 0 1 φ := by simpa using rel 1 1 0 1
  have rdc : E 1 1 (E 1 0 φ) - E 1 0 (E 1 1 φ) = E 1 0 φ := by simpa using rel 1 1 1 0
  have rbc : E 0 1 (E 1 0 φ) - E 1 0 (E 0 1 φ) = E 0 0 φ - E 1 1 φ := by simpa using rel 0 1 1 0
  have rad : E 0 0 (E 1 1 φ) - E 1 1 (E 0 0 φ) = 0 := by simpa using rel 0 0 1 1
  have t1 : ∀ X : Module.End ℂ V, X (E 0 0 φ) + X (E 1 1 φ) = 0 := fun X => by
    rw [← map_add (f := _), h1, map_zero]
  have t2 : ∀ X : Module.End ℂ V,
      X (E 0 1 φ) - X (E 1 0 φ) = (Complex.I * k) • X φ := fun X => by
    rw [← map_sub, h2, map_smul]
  have t3 : ∀ X : Module.End ℂ V, X (E 0 0 φ) - X (E 1 1 φ) =
      Complex.I • (X (E 0 1 φ) + X (E 1 0 φ)) := fun X => by
    rw [← map_sub, h3, map_smul, map_add (f := _)]
  have hc : (E 0 0 (E 0 0 φ) - E 0 0 (E 1 1 φ) - E 1 1 (E 0 0 φ) + E 1 1 (E 1 1 φ)) +
      (E 0 1 (E 0 1 φ) + E 0 1 (E 1 0 φ) + E 1 0 (E 0 1 φ) + E 1 0 (E 1 0 φ)) =
      (-2 * k) • φ := by
    linear_combination (norm := module)
      (t3 (E 0 0) - t3 (E 1 1) + Complex.I • t3 (E 0 1) + Complex.I • t3 (E 1 0)) +
        Complex.I • (rab + rac - rdb - rdc) + (2 * Complex.I) • h2 +
        Complex.I_sq • (E 0 1 (E 0 1 φ) + E 0 1 (E 1 0 φ) + E 1 0 (E 0 1 φ) + E 1 0 (E 1 0 φ) +
          (2 * k) • φ)
  have hw : E 0 1 (E 0 1 φ) - E 0 1 (E 1 0 φ) - E 1 0 (E 0 1 φ) + E 1 0 (E 1 0 φ) =
      (-k ^ 2) • φ := by
    linear_combination (norm := module)
      (t2 (E 0 1) - t2 (E 1 0)) + (Complex.I * k) • h2 + Complex.I_sq • (k ^ 2 • φ)
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  have hq : ∀ v : ℂ, qdet E v φ =
      v • ((v - 1) • φ + E 1 1 φ) + ((v - 1) • E 0 0 φ + E 0 0 (E 1 1 φ)) - E 1 0 (E 0 1 φ) := by
    intro v
    unfold qdet qminor Tm
    rw [hu, Finset.sum_pair hne]
    simp [List.ofFn_succ, Module.algebraMap_end_apply]
    module
  rw [hq]
  linear_combination (norm := module)
    u • h1 + (1 / 4 : ℂ) • (t1 (E 0 0) + t1 (E 1 1)) + (1 / 2 : ℂ) • rad - (1 / 4 : ℂ) • hc +
      (1 / 4 : ℂ) • hw + (1 / 2 : ℂ) • rbc

end UpperTheory.Reformulated.B.Qf10
