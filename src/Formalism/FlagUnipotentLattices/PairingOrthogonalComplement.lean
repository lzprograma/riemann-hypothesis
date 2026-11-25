module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.SobolevGaussianKernels.StatementEI, Formalism.FlagUnipotentLattices.PairingOrthogonalComplement

-- ===== clump member: Formalism.SobolevGaussianKernels.StatementEI =====
-- clump-header: {"m": "Formalism.SobolevGaussianKernels.StatementEI", "h": "module\n\npublic import Mathlib.Algebra.Algebra.Basic\npublic import Mathlib.Algebra.Module.LinearMap.Star\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.SL.IwahoriBlocks

variable {E : Type*} [CommRing E] [StarRing E] {V : Type*} [AddCommGroup V] [Module E V]

def IsHerm (h : V →ₗ[E] V →ₗ⋆[E] E) : Prop := ∀ v w, h w v = star (h v w)

def eich (h : V →ₗ[E] V →ₗ⋆[E] E) (x u : V) (s : E) (v : V) : V :=
  v + h v u • x - h v x • (u + s • x)

end Formalism.SL.IwahoriBlocks
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.SobolevGaussianKernels.StatementEI =====

-- ===== clump member: Formalism.FlagUnipotentLattices.PairingOrthogonalComplement =====
-- clump-header: {"m": "Formalism.FlagUnipotentLattices.PairingOrthogonalComplement", "h": "module\n\npublic import Mathlib.Analysis.SpecialFunctions.Pow.Real\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import Formalism.SobolevGaussianKernels.StatementEI\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.HermitianLatticeCounting.S4

open Finset
open Formalism.SL.IwahoriBlocks (IsHerm eich)

def ValuationProductBound : Prop :=
  ∀ (B : Type) [Fintype B] (s : B → ℕ) (vh ve vt : B → ℝ) (q A : ℝ) (r : ℕ),
    1 ≤ q → (∀ b, 1 ≤ s b ∧ s b ≤ r + 1) → (∀ b, 0 ≤ vh b) → (∀ b, 0 ≤ ve b) →
    (∀ b, (s b : ℝ) * vt b = ve b - vh b) → ∑ b, vh b ≤ A → ∑ b, ve b ≤ A →
    ∏ b, q ^ (2 * (s b : ℝ) * vh b) ≤ (q ^ A) ^ (2 * ((r : ℝ) + 1)) ∧
    ∏ b, q ^ (vt b * ((s b : ℝ) * ((s b : ℝ) - 1) / 2)) ≤ (q ^ A) ^ (((r : ℝ) + 1) / 2)

def WeightedCS : Prop :=
  ∀ (ι : Type) [Fintype ι] (V : Type) [SeminormedAddCommGroup V] (v : ι → V) (W : ι → ℝ),
    (∀ i, 0 < W i) → ‖∑ i, v i‖ ^ 2 ≤ (∑ i, (W i)⁻¹) * ∑ i, W i * ‖v i‖ ^ 2

def OmCount : Prop :=
  ∀ (P : Type) (Om : Finset P) (H : P → ℝ), (∀ p ∈ Om, 2 ≤ H p) → (2 : ℝ) ^ Om.card ≤ ∏ p ∈ Om, H p

def Step4 : Prop :=
  ∀ (P : Type) [Fintype P] [DecidableEq P] (Om : Finset P) (D : P → Type) [∀ p, Fintype (D p)]
    (w : ∀ p, D p → ℝ) (aN aZ : ∀ p, D p → ℂ) (H nn ngen : P → ℝ) (q : P → ℕ) (c κ : ℕ),
    (∀ p d, 0 ≤ w p d) → (∀ p, 1 ≤ H p) → (∀ p, 2 ≤ q p) → (∀ p, 0 ≤ nn p) →
    (∀ p ∈ Om, ∑ d, w p d * ‖aN p d‖ ^ 2 ≤ H p ^ c * ((q p : ℝ) ^ κ)⁻¹ * nn p) →
    (∀ p, ∑ d, w p d * ‖aZ p d‖ ^ 2 ≤ H p ^ c * nn p) →
    (∀ p, nn p ≤ H p ^ c * ngen p) →
    ∑ d : (∀ p, D p), (∏ p, w p (d p)) *
        ‖∑ A ∈ Om.powerset.filter (fun A => A.Nonempty),
            ∏ p, (if p ∈ A then aN p (d p) else aZ p (d p))‖ ^ 2
      ≤ (4 : ℝ) ^ Om.card * (∏ p, H p) ^ (2 * c) * ((2 : ℝ) ^ κ)⁻¹ * ∏ p, ngen p

end Formalism.HermitianLatticeCounting.S4
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.FlagUnipotentLattices.PairingOrthogonalComplement =====
