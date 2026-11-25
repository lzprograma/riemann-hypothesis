module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Polynomial GlobalTheory.GLq

namespace GlobalTheory.Published

def IsRegularChar (g d : ℕ) {K : Type} [Field K] (θ : Kˣ →* ℂˣ) : Prop :=
  ∀ i j, i < d → j < d → θ ^ g ^ i = θ ^ g ^ j → i = j

/-- **Green's parametrisation of the cuspidal characters of `GL_d(𝔽_g)`**, for a prime `g`.
Let `d > 0` and let `K` be the field with `g ^ d` elements. Call a character `θ` of `Kˣ`
regular if `θ, θ ^ g, …, θ ^ (g ^ (d - 1))` are distinct (`IsRegularChar`). Then there is a
map `θ ↦ τ θ` to functions on `GL_d(𝔽_g)` such that:
* for regular `θ`, `τ θ` is an irreducible cuspidal character (`IsCusp`) of degree
  `(g - 1) (g ^ 2 - 1) ⋯ (g ^ (d - 1) - 1)`, and at an element whose characteristic polynomial
  is irreducible with a root `z ∈ Kˣ` it takes the value
  `(-1) ^ (d - 1) * (θ z + θ (z ^ g) + ⋯ + θ (z ^ (g ^ (d - 1))))`;
* for regular `θ` and `θ'`, `τ θ = τ θ'` exactly when `θ' = θ ^ (g ^ i)` for some `i < d`;
* every irreducible cuspidal character of `GL_d(𝔽_g)` is `τ θ` for some regular `θ`. -/
def GreenRegularCharacters : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K], Module.finrank (ZMod g) K = d →
    ∃ τ : (Kˣ →* ℂˣ) → Gn g d → ℂ,
      (∀ θ, IsRegularChar g d θ → IsCusp (τ θ) ∧ τ θ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ∧
        ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g d).charpoly = 0 →
          τ θ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, ((θ (z ^ g ^ i) : ℂˣ) : ℂ)) ∧
      (∀ θ θ', IsRegularChar g d θ → IsRegularChar g d θ' → (τ θ = τ θ' ↔ ∃ i < d, θ' = θ ^ g ^ i)) ∧
      ∀ χ : Gn g d → ℂ, IsCusp χ → ∃ θ, IsRegularChar g d θ ∧ χ = τ θ

end GlobalTheory.Published

end
