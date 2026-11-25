module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvariantDerivAlongEndo
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.NabTrans

@[expose] public section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.PullbackColumn

variable {k : Type} [CommRing k] {d : ℕ}

theorem expS_pow [Algebra ℚ k] {n : ℕ} (g : PS k n d) (hg : constantCoeff g = 0) (m : ℕ) :
    FB.expS k g ^ m = FB.expS k ((m : k) • g) := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, zero_smul, nt_expS_zero]
  | succ m ih =>
    rw [pow_succ, ih, Nat.cast_succ, add_smul, one_smul,
      gt_expS_add _ _ (by rw [nt_const_smul, hg, mul_zero]) hg]

theorem dpolyOf_monomial_one (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
    (mo : ι →₀ ℕ) (g : PS k 1 d) :
    DpolyOf F u (MvPolynomial.monomial mo (1 : k)) g = DmonOf F u mo g := by
  classical
  have e : DpolyOf F u (MvPolynomial.monomial mo (1 : k)) g =
      ∑ m ∈ ({mo} : Finset (ι →₀ ℕ)), C ((MvPolynomial.monomial mo (1 : k)).coeff m) * DmonOf F u m g := by
    unfold DpolyOf
    refine Finset.sum_subset MvPolynomial.support_monomial_subset fun x _ hx => ?_
    rw [MvPolynomial.notMem_support_iff.1 hx, map_zero, zero_mul]
  rw [e, Finset.sum_singleton, MvPolynomial.coeff_monomial, ite_eq_left rfl, map_one, one_mul]

end GlobalTheory.PullbackColumn

namespace GlobalTheory

open PullbackColumn

theorem nabVal_pullback_monomial : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 a : O) (N m : ℕ) (w : PS R 1 d), FB.toK k w = FB.expS k (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) → ∀ (ι : Type) [Fintype ι] (u : ι → Fin d → k) (α : ι → k), (∀ l, (dAct k B a).mulVec (u l) = α l • u l) → ∀ (f : PS k 1 d) (mo : ι →₀ ℕ), B.nabVal k h w0 (N * m) (ev (n := 1) ![B.actK k a] f * FB.toK k w ^ m) u (MvPolynomial.monomial mo 1) = (∏ l, α l ^ mo l) * B.nabVal k h w0 m f u (MvPolynomial.monomial mo 1) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 a N m w hw ι _ u α hα f mo
  have hA : ∀ b : O, GP (B.actK k b) := fun b => QuadDeriv.constantCoeff_mapP_eq_zero _ _ (B.A.const b)
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have cL : constantCoeff (B.hL k h w0) = 0 :=
    gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ (hA w0) (gp_pt 0))) h hh0
  have cA : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0)) = 0 :=
    gt_const_ev _ (single_point_zero_constant (hA a)) _ cL
  have cD : constantCoeff (ev (n := 1) ![B.actK k a] (B.hL k h w0) - (N : k) • B.hL k h w0) = 0 := by
    rw [map_sub, cA, nt_const_smul, cL, mul_zero, sub_zero]
  have hG : ev (n := 1) ![B.actK k a] f * FB.toK k w ^ m * FB.expS k (((N * m : ℕ) : k) • B.hL k h w0) =
      ev (n := 1) ![B.actK k a] (f * FB.expS k ((m : k) • B.hL k h w0)) := by
    rw [hw, expS_pow _ cD, mul_assoc, ← gt_expS_add _ _ (by rw [nt_const_smul, cD, mul_zero])
      (by rw [nt_const_smul, cL, mul_zero]), gt_ev_mul _ (single_point_zero_constant (hA a)),
      gt_ev_expS _ (single_point_zero_constant (hA a)) _ (by rw [nt_const_smul, cL, mul_zero]), nt_ev_smul _ (single_point_zero_constant (hA a)),
      smul_sub, smul_smul, Nat.cast_mul, mul_comm (N : k) (m : k), sub_add_cancel]
  unfold FB.nabVal
  rw [hG, dpolyOf_monomial_one, dpolyOf_monomial_one]
  exact (invariantDeriv_along_endo R d O k B a).2 ι u α hα mo _

end GlobalTheory
