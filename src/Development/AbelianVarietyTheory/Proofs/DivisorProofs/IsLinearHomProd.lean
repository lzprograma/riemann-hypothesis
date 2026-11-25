module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.HomLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

def coords : Set (Fin p → E) :=
  {c | ∃ n : ℕ, 0 < n ∧ ∃ x : Fin p → 𝓞 E, (∀ a, (x a : E) = n * c a) ∧
    ∃ f : (X.A true).t.G ⟶ X.B.t.G, Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
      f ^ n = ∏ a, ((X.A true).t.act.act (x a) ≫ phiP X a)}

def lat : Submodule (𝓞 E) (Fin p → E) := Submodule.span (𝓞 E) (coords X)

theorem isLinearHom_prod (x : Fin p → 𝓞 E) :
    Serre.IsLinearHom (X.A true).t.act X.B.t.act (∏ a, ((X.A true).t.act.act (x a) ≫ phiP X a)) := by
  classical
  refine Finset.prod_induction _ (Serre.IsLinearHom (X.A true).t.act X.B.t.act)
    (fun f g hf hg => hf.mul hg) (Serre.IsLinearHom.one _ _) fun a _ => ?_
  exact (Serre.IsLinearHom.act _ _).comp (X.lin (Sum.inl a))

theorem intl_mem (x : Fin p → 𝓞 E) : (fun a => (x a : E)) ∈ lat X :=
  Submodule.subset_span ⟨1, one_pos, x, fun a => by simp, _, isLinearHom_prod X x, pow_one _⟩

end GlobalTheory.FlatCM.HomLat

end
