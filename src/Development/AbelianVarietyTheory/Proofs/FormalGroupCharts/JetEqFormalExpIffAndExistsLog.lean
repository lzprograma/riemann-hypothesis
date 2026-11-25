module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import Mathlib.RingTheory.PowerSeries.Log

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem jeq_pow_congr {R σ : Type} [CommRing R] {m : ℕ} {a b : MvPowerSeries σ R} (h : JEq m a b) (n : ℕ) :
    JEq m (a ^ n) (b ^ n) := by
  classical
  induction n with
  | zero => intro e _; rw [pow_zero, pow_zero]
  | succ n ih =>
    intro e he
    rw [pow_succ, pow_succ, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hd : p.1.degree + p.2.degree = e.degree := by rw [← map_add (f := _), hp]
    rw [ih p.1 (by omega), h p.2 (by omega)]

theorem jeq_psubst_congr {R σ : Type} [CommRing R] {m : ℕ} {a b : MvPowerSeries σ R}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (h : JEq m a b)
    (F : PowerSeries R) : JEq m (PowerSeries.subst a F) (PowerSeries.subst b F) := by
  intro e he
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hb)]
  refine finsum_congr fun n => ?_
  rw [jeq_pow_congr h n e he]

theorem jeq_expS_iff_and_exists_log : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (n d m : ℕ), (∀ f g : PS k n d, MvPowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff g = 0 → (JEq m f g ↔ JEq m (FB.expS k f) (FB.expS k g))) ∧ ∀ u : PS k n d, MvPowerSeries.constantCoeff u = 1 → ∃ lam : PS k n d, MvPowerSeries.constantCoeff lam = 0 ∧ FB.expS k lam = u := by
  intro k _ _ n d m
  refine ⟨fun f g hf hg => ⟨fun h => jeq_psubst_congr hf hg h _, fun h => ?_⟩, fun u hu => ?_⟩
  · have h1 : JEq m (PowerSeries.subst f (PowerSeries.exp k) - 1) (PowerSeries.subst g (PowerSeries.exp k) - 1) := by
      intro e he
      rw [map_sub, map_sub]
      exact congrArg (· - _) (h e he)
    have h2 := jeq_psubst_congr (by simp [TB.WickVanishing.constantCoeff_exp hf]) (by simp [TB.WickVanishing.constantCoeff_exp hg]) h1
      (PowerSeries.log k)
    rwa [TB.WickVanishing.log_exp hf, TB.WickVanishing.log_exp hg] at h2
  · exact ⟨_, TB.WickVanishing.constantCoeff_logS hu, TB.WickVanishing.exp_log hu⟩

end GlobalTheory.ChartCmp
