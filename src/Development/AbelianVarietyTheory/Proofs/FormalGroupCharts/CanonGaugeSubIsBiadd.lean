module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

@[expose] public section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory

theorem canonGauge_sub_isBiadd : G2.CanonicalGaugeDiffBiadditive := by
  intro R _ d O _ _ k _ _ _ B h h' hh hh'
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hz : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hF : ∀ i, constantCoeff (B.FK k i) = 0 := fun i => by
    simp only [FB.FK, FGLaw.mapF, MvPowerSeries.constantCoeff_map, B.G.const i, map_zero]
  have hA : ∀ a, GP (B.actK k a) := fun a i => by
    simp only [FB.actK, MvPowerSeries.constantCoeff_map, B.A.const a i, map_zero]
  have h0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_zero] at this
  have h0' : constantCoeff h' = 0 := by
    have := congrArg constantCoeff hh'.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz (hp 0)), map_zero] at this
  have inj : ∀ {n : ℕ} {a b : PS k n d}, constantCoeff a = 0 → constantCoeff b = 0 →
      FB.expS k a = FB.expS k b → a = b := fun ha hb e => exp_inj ha hb e
  refine ⟨?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_sub _ (pair_points_zero_constant hz (hp 0)), hh.ax0, hh'.ax0, sub_zero]
  · rw [gt_ev_sub _ (pair_points_zero_constant (hp 0) hz), hh.ax1, hh'.ax1, sub_zero]
  · have a1 := pair_points_zero_constant (hp (n := 3) 0) (hp 2)
    have a2 := pair_points_zero_constant (hp (n := 3) 1) (hp 2)
    have a3 := pair_points_zero_constant (gp_addOf _ hF _ _ (hp (n := 3) 0) (hp 1)) (hp 2)
    have e := inj
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, gt_const_ev _ a3 _ h0]; simp)
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', gt_const_ev _ a3 _ h0']; simp)
      (hh.ph1.symm.trans hh'.ph1)
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2, gt_ev_sub _ a3]
    linear_combination -e
  · have a1 := pair_points_zero_constant (hp (n := 3) 0) (hp 1)
    have a2 := pair_points_zero_constant (hp (n := 3) 0) (hp 2)
    have a3 := pair_points_zero_constant (hp (n := 3) 0) (gp_addOf _ hF _ _ (hp (n := 3) 1) (hp 2))
    have e := inj
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, gt_const_ev _ a3 _ h0]; simp)
      (by rw [map_sub, map_add (f := _), gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', gt_const_ev _ a3 _ h0']; simp)
      (hh.ph2.symm.trans hh'.ph2)
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2, gt_ev_sub _ a3]
    linear_combination -e
  · have a1 := pair_points_zero_constant (gp_comp1 _ _ (hA a) (hp (n := 2) 0)) (hp 1)
    have a2 := pair_points_zero_constant (hp (n := 2) 0) (gp_comp1 _ _ (hA (star a)) (hp (n := 2) 1))
    have e := inj
      (by rw [map_sub, gt_const_ev _ a1 _ h0, gt_const_ev _ a2 _ h0, sub_zero])
      (by rw [map_sub, gt_const_ev _ a1 _ h0', gt_const_ev _ a2 _ h0', sub_zero])
      ((hh.ad a).symm.trans (hh'.ad a))
    rw [gt_ev_sub _ a1, gt_ev_sub _ a2]
    linear_combination -e

end GlobalTheory
