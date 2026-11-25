module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.ZH

theorem exists_test_match : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ x, y₀ ⟨S.th x, S.th_mem x⟩ ≠ 0 → ∃ w : u.D.toPre.X, l.yy x = QuotientAddGroup.mk w ∧ ‖y₀ ⟨S.th x, S.th_mem x⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) → (0 < S.delta y₀ ∧ AddSubgroup.closure {x | ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = S.delta y₀} = l.yy.ker) → (∀ α : u.D.toPre.X, (∀ v₀, l.q α ≤ l.q (α + S.N • v₀)) → ∀ h ∈ l.yy.ker, ∀ i, ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt α) j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q α / S.N))) → (∀ α : u.D.toPre.X, (∀ v₀, l.q α ≤ l.q (α + S.N • v₀)) → ∃ (k : _) (hk : S.FF _ (l.wt α) k ∈ S.R), ‖y₀ ⟨S.FF _ (l.wt α) k, hk⟩‖ = S.delta y₀ * Real.exp (-(l.q α / S.N))) → (∀ h ∈ l.yy.ker, ∃ i, ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt 0) j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ = S.delta y₀) → ∃ τ : S.Test p y₀, l.Match τ := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u l h1 h2 h3 h4 h5
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have hmax : IsGreatest (Set.range fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) (S.delta y₀) := by
    obtain ⟨x, hx⟩ := exists_eq_ciSup_of_finite (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖)
    refine ⟨⟨x, hx⟩, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact le_ciSup (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) (Set.finite_range _).bddAbove z
  let τ : S.Test p y₀ :=
    { X := u.D.toPre.X
      q := l.q
      pos := l.pos
      yy := l.yy
      yy_onto := l.yy_onto
      isoFree := l.isoFree
      wt := l.wt
      wt_eq := l.wt_eq
      δ := S.delta y₀
      δ_max := hmax
      δ_pos := h2.1
      supp := h2.2
      tx := h1
      le := h3
      eq := h4
      unit0 := h5 }
  exact ⟨τ, AddEquiv.refl _, fun _ => rfl, fun _ _ => Iff.rfl⟩
end GlobalTheory.ZH
