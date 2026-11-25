module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries

@[expose] public section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.CrudeValue

variable {k : Type} [CommRing k] {d : ℕ}

theorem constantCoeff_expS [Algebra ℚ k] {n : ℕ} (g : PS k n d) (hg : constantCoeff g = 0) :
    constantCoeff (FB.expS k g) = 1 := by
  unfold FB.expS
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hg),
    finsum_eq_single _ 0]
  · simp
  · intro j hj
    rw [map_pow, hg, zero_pow hj, smul_zero]

theorem constantCoeff_ev_eq_zero {m n : ℕ} (a : Fin m → Pt k n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS k m d) (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 := by
  have ha' : ∀ q : Fin m × Fin d, constantCoeff ((fun q : Fin m × Fin d => a q.1 q.2) q) = 0 :=
    fun q => ha q.1 q.2
  unfold ev
  exact constantCoeff_subst_eq_zero (a := fun q : Fin m × Fin d => a q.1 q.2)
    (hasSubst_of_constantCoeff_zero ha') ha' hf

variable {R : Type} [CommRing R] {O : Type} [CommRing O] [StarRing O] [Algebra ℚ k] [Algebra R k]


omit [Algebra ℚ k] in
theorem constantCoeff_hL (B : FB R d O) (h : PS k 2 d) (hh : constantCoeff h = 0) (w0 : O) :
    constantCoeff (B.hL k h w0) = 0 := by
  have hp : ∀ i, constantCoeff (pt k (n := 1) d 0 i) = 0 := fun i => constantCoeff_X _
  refine constantCoeff_ev_eq_zero _ (fun j i => ?_) h hh
  fin_cases j
  · exact hp i
  · refine constantCoeff_ev_eq_zero ![pt k d 0] (fun j i' => ?_) (B.actK k w0 i) ?_
    · fin_cases j
      exact hp i'
    · unfold FB.actK
      rw [constantCoeff_map, B.A.const, map_zero]

theorem nabVal_monomial (B : FB R d O) (h : PS k 2 d) (w0 : O) (q : ℕ) (f : PS k 1 d) {ι : Type}
    [Fintype ι] (u : ι → Fin d → k) (e : ι →₀ ℕ) :
    B.nabVal k h w0 q f u (MvPolynomial.monomial e 1) =
      constantCoeff (DmonOf (B.G.mapF (algebraMap R k)) u e
        (f * FB.expS k ((q : k) • B.hL k h w0))) := by
  classical
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  · simp only [FB.nabVal, FB.FK, DpolyOf, MvPolynomial.support_monomial,
      ite_eq_right (one_ne_zero : (1 : k) ≠ 0), Finset.sum_singleton, MvPolynomial.coeff_monomial,
      ite_true, map_one, one_mul]

end GlobalTheory.CrudeValue
