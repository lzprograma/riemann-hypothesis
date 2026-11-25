module

public import GroundTheory.AutomorphicForms.GL2.GJFEDefs
public import Formalism.DoubleCosetMeasures.Statement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel


namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

def GxShape (q : ℂ) (γ : RatFunc ℂ) (P : ℂ[X]) : Prop :=
  ∃ (c : ℂ) (j : ℤ), c ≠ 0 ∧
    γ = RatFunc.C c * RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) P / algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C q * X))

theorem gxShape_one (q : ℂ) : GxShape q 1 1 := ⟨1, 0, one_ne_zero, by simp⟩

theorem gxShape_mul {q : ℂ} {γ₁ γ₂ : RatFunc ℂ} {P₁ P₂ : ℂ[X]} (h₁ : GxShape q γ₁ P₁) (h₂ : GxShape q γ₂ P₂) :
    GxShape q (γ₁ * γ₂) (P₁ * P₂) := by
  obtain ⟨c₁, j₁, hc₁, rfl⟩ := h₁
  obtain ⟨c₂, j₂, hc₂, rfl⟩ := h₂
  refine ⟨c₁ * c₂, j₁ + j₂, mul_ne_zero hc₁ hc₂, ?_⟩
  rw [Polynomial.mul_comp, map_mul, map_mul, map_mul, zpow_add₀ RatFunc.X_ne_zero]
  ring

def GxBlock : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (m : ℕ) [NeZero m]
    [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)] (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure]
    (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] [SecondCountableTopology H] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin m) F × H) W),
    IsAdmissible σ → σ.IsIrreducible → ∀ α : ℂ, α ≠ 0 → (∀ v, σ (centralUnif F m, 1) v = α • v) →
    (∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ), ∃ C : Set (GL (Fin m) F), IsCompact C ∧
      ∀ g, ℓ (σ (g, 1) v) ≠ 0 → ∃ j : ℤ, centralUnif F m ^ j * g ∈ C) →
    ∀ ψ : AddChar F Circle, Continuous ψ → ψ ≠ 1 → ∀ γ : RatFunc ℂ,
    (∀ Φ : Matrix (Fin m) (Fin m) F → ℂ, IsSchwartzBruhat Φ → ∀ v : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      RatFE F γ (blockA μ σ Φ v ℓ) (blockB μ σ (GJMatrix.localMatrixFourier ψ Φ) v ℓ)) →
    GxShape ((GroundTheory.LocalField.residueCard F : ℕ) : ℂ) γ
      (if m = 1 ∧ ∀ g ∈ integralGL F m, σ (g, 1) = 1 then 1 - C α * X else 1)

def polF {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ} {β : Fin n → ℕ}
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W) (α : Set.range β → ℂ) : ℂ[X] :=
  ∏ a : Set.range β, if blockSize β a = 1 ∧ ∀ g ∈ integralGL F (blockSize β a),
    σ ((leviEquivPi F β).symm (Pi.mulSingle a g)) = 1 then 1 - C (α a) * X else 1

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
