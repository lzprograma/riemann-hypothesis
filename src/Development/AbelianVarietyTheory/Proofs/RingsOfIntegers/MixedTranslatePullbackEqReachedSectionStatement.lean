module

public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueNormalisedPullbackRationalNorm
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsNormalisedPullbackSectionMul
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Tactic.Basify

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSection, Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSectionStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSection =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSection", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd\npublic import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueNormalisedPullbackRationalNorm\npublic import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel\npublic import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsNormalisedPullbackSectionMul\npublic import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations\npublic import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem uu_eq_pull_reach : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (N n' A Bn : ℕ) (α β : 𝓞 E), Odd N → (N : 𝓞 E) = β * α * n' → α * H.bar α = (A : 𝓞 E) → β * H.bar β = (Bn : 𝓞 E) → ∀ (s : SecN Xo x 1) (x₁ x₂ : (ptO Xo x ⟶ Xo.univ.t.G)) (F), x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → (x₁ ≫ Xo.univ.t.act.act (α * β)) ^ (n' ^ 2) = 1 → (x₂ ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * A) = 1 → IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F → N ^ 2 = n' ^ 2 * A * Bn ∧ ∃ hh : SecN Xo x (n' ^ 2 * A), Reach Xo s (n' ^ 2 * A) hh ∧ Pulls Xo β hh (sqN Xo N F) := by
  intro E _ _ _ H Dw l Xo S _ x N n' A Bn α β hodd hN hα hβ s x₁ x₂ F h₁ h₂ h₁' h₂' hUU
  have hαβ : (α * β) * H.bar (α * β) = ((A * Bn : ℕ) : 𝓞 E) := by
    rw [map_mul, Nat.cast_mul, ← hα, ← hβ]; ring
  have hn : (n' : 𝓞 E) * H.bar (n' : 𝓞 E) = ((n' ^ 2 : ℕ) : 𝓞 E) := by
    rw [map_natCast, Nat.cast_pow]; ring
  have hNN : (N : 𝓞 E) * H.bar (N : 𝓞 E) = ((N ^ 2 : ℕ) : 𝓞 E) := by
    rw [map_natCast, Nat.cast_pow]; ring
  have hN' : (n' : 𝓞 E) * (α * β) = (N : 𝓞 E) := by rw [hN]; ring
  have hsq : N ^ 2 = n' ^ 2 * A * Bn := by
    have h : ((N ^ 2 : ℕ) : 𝓞 E) = ((n' ^ 2 * A * Bn : ℕ) : 𝓞 E) := by
      rw [← hNN, ← hN', map_mul, mul_assoc (n' ^ 2), Nat.cast_mul (n' ^ 2), ← hn, ← hαβ]; ring
    exact_mod_cast h
  have hoN : Odd (N ^ 2) := hodd.pow
  have ho3 : Odd (n' ^ 2 * A * Bn) := hsq ▸ hoN
  have ho2 : Odd (n' ^ 2 * A) := (Nat.odd_mul.1 ho3).1
  have ho1 : Odd (n' ^ 2) := (Nat.odd_mul.1 ho2).1
  have hoA : Odd A := (Nat.odd_mul.1 ho2).2
  have hlev : n' ^ 2 = 1 ∨ 4 ≤ n' ^ 2 := by
    rcases n' with _ | _ | m
    · simp at ho1
    · left; rfl
    · right; exact Nat.pow_le_pow_left (n := 2) (by omega) 2
  refine ⟨hsq, ?_⟩
  obtain ⟨F₀, F₁, hF₀, hF₁, hF₂⟩ := ((_root_.GlobalTheory.PlaceInt.uu_through_moves E H Dw l Xo S x N hodd s).1 x₁ x₂ F h₁ h₂).1 hUU
  obtain ⟨G₀, hG₀, -⟩ := _root_.GlobalTheory.existsUnique_pulls E H Dw l Xo S x (n' : 𝓞 E) (n' ^ 2) 1 (n' ^ 2) hn (Nat.one_mul _).symm s
  obtain ⟨G₁, hG₁, -⟩ := (_root_.GlobalTheory.existsUnique_moves E H Dw l Xo S x (n' ^ 2) ho1 _ h₁' G₀).1
  obtain ⟨K₁, hK₁, -⟩ := _root_.GlobalTheory.existsUnique_pulls E H Dw l Xo S x α A (n' ^ 2) (n' ^ 2 * A) hα rfl G₁
  obtain ⟨hh, hhh, -⟩ := (_root_.GlobalTheory.existsUnique_moves E H Dw l Xo S x (n' ^ 2 * A) ho2 _ h₂' K₁).1
  refine ⟨hh, ?_, ?_⟩
  · refine Reach.move _ _ K₁ hh (Reach.pull (n' ^ 2) A _ α G₁ K₁ ?_ hlev hoA hα rfl hK₁) hhh
    refine Reach.move _ _ G₀ G₁ ?_ hG₁
    exact Reach.pull 1 (n' ^ 2) _ _ s G₀ Reach.base (Or.inl rfl) ho1 hn (Nat.one_mul _).symm hG₀
  · have hsq' : N ^ 2 = n' ^ 2 * (A * Bn) := by rw [hsq, Nat.mul_assoc]
    obtain ⟨P, hP, -⟩ := _root_.GlobalTheory.existsUnique_pulls E H Dw l Xo S x (α * β) (A * Bn) (n' ^ 2) (N ^ 2) hαβ hsq' G₀
    obtain ⟨Q, hQ, -⟩ := _root_.GlobalTheory.existsUnique_pulls E H Dw l Xo S x β Bn (n' ^ 2 * A) (N ^ 2) hβ hsq K₁
    obtain ⟨R, hR, -⟩ := _root_.GlobalTheory.existsUnique_pulls E H Dw l Xo S x β Bn (n' ^ 2 * A) (N ^ 2) hβ hsq hh
    have hPN : Pulls Xo (N : 𝓞 E) s P := hN' ▸ _root_.GlobalTheory.PullComp.pulls_mul E H Dw l Xo S x _ _ _ _ _ s G₀ P hG₀ hP
    have hPF : P = F₀ :=
      (_root_.GlobalTheory.existsUnique_pulls E H Dw l Xo S x (N : 𝓞 E) (N ^ 2) 1 (N ^ 2) hNN (Nat.one_mul _).symm s).unique hPN hF₀
    have hQ' : Pulls Xo (α * β) G₁ Q := _root_.GlobalTheory.PullComp.pulls_mul E H Dw l Xo S x _ _ _ _ _ G₁ K₁ Q hK₁ hQ
    have hm₁ : Moves Xo x₁ P Q :=
      _root_.GlobalTheory.PlaceInt.moves_of_pulls E H Dw l Xo S x (α * β) (A * Bn) _ _ hαβ hsq' hoN _ x₁ rfl h₁ G₀ G₁ P Q hG₁ hP hQ'
    have hQF : Q = F₁ := (_root_.GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hoN x₁ h₁ F₀).1.unique (hPF ▸ hm₁) hF₁
    have hm₂ : Moves Xo x₂ Q R :=
      _root_.GlobalTheory.PlaceInt.moves_of_pulls E H Dw l Xo S x β Bn _ _ hβ hsq hoN _ x₂ rfl h₂ K₁ hh Q R hhh hQ hR
    have hRF : R = sqN Xo N F := (_root_.GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hoN x₂ h₂ F₁).1.unique (hQF ▸ hm₂) hF₂
    exact hRF ▸ hR

end GlobalTheory.PlaceInt
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSection =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSectionStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSectionStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd\npublic import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSection\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.mixed_translate_pullback_eq_reached_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (N n' A Bn : ℕ) (α β : 𝓞 E), Odd N → (N : 𝓞 E) = β * α * n' → α * H.bar α = (A : 𝓞 E) → β * H.bar β = (Bn : 𝓞 E) → ∀ (s : SecN Xo x 1) (x₁ x₂ : (ptO Xo x ⟶ Xo.univ.t.G)) (F), x₁ ^ (N ^ 2) = 1 → x₂ ^ (N ^ 2) = 1 → (x₁ ≫ Xo.univ.t.act.act (α * β)) ^ (n' ^ 2) = 1 → (x₂ ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * A) = 1 → IsUUOver Xo.univ.t.G Xo.univ.t.PP N s x₁ x₂ F → N ^ 2 = n' ^ 2 * A * Bn ∧ ∃ hh : SecN Xo x (n' ^ 2 * A), Reach Xo s (n' ^ 2 * A) hh ∧ Pulls Xo β hh (sqN Xo N F) := by
  first | exact @GlobalTheory.PlaceInt.uu_eq_pull_reach
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MixedTranslatePullbackEqReachedSectionStatement =====
