module

import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompletedLFunctionNeZeroOfReNonpos
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivRiemannZetaLocalZeroSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Lemma
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

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

open Filter Topology
open scoped Classical

namespace GlobalTheory.PrincipalLogDeriv

open Filter Topology

lemma norm_cpow_neg_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  calc (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2

private lemma hasDerivAt_factor_mul (a : ℂ) {p : ℕ} (hp : p.Prime) (s : ℂ) :
    HasDerivAt (fun z : ℂ => 1 - a * (p : ℂ) ^ (-z))
      (a * (p : ℂ) ^ (-s) * Complex.log p) s := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  convert ((((hasDerivAt_id' s).neg).const_cpow (Or.inl hp0)).const_mul a).const_sub 1 using 1
  simp only [Pi.neg_apply]
  ring


private lemma norm_logDeriv_factor_mul_le (a : ℂ) (ha : ‖a‖ ≤ 1) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (fun z : ℂ => 1 - a * (p : ℂ) ^ (-z)) s‖ ≤ Real.log p := by
  have h1 : ‖a * (p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_mul]
    calc ‖a‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right ha (norm_nonneg _)
      _ ≤ 1 / 2 := by simpa using norm_cpow_neg_le hp hs
  have h2 : 1 / 2 ≤ ‖1 - a * (p : ℂ) ^ (-s)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (a * (p : ℂ) ^ (-s))
    rw [norm_one] at h
    linarith
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p), Complex.norm_real,
      Real.norm_of_nonneg hl]
  rw [logDeriv_apply, (hasDerivAt_factor_mul a hp s).deriv, norm_div, norm_mul, hlog,
    div_le_iff₀ (by linarith)]
  nlinarith




lemma sum_log_primeFactors_le (q : ℕ) [NeZero q] :
    ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  · have h := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
    rw [← Nat.cast_prod]
    exact_mod_cast h

/-- In the closed right half-plane, only newly introduced prime Euler factors
contribute to the logarithmic-derivative correction under a change of level. -/
theorem norm_logDeriv_changeLevel_sub_le_sum {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) {s : ℂ}
    (hs : 1 ≤ s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) :
    ‖deriv (LFunction (changeLevel hMN χ)) s / LFunction (changeLevel hMN χ) s -
      deriv (LFunction χ) s / LFunction χ s‖ ≤ ∑ p ∈ N.primeFactors \ M.primeFactors, Real.log p := by
  classical
  have hev : LFunction (changeLevel hMN χ) =ᶠ[𝓝 s] fun z => LFunction χ z *
      ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-z)) := by
    have hnear : ∀ᶠ z in 𝓝 s, χ ≠ 1 ∨ z ≠ 1 := by
      rcases hχs with hχ | hs1
      · exact Filter.Eventually.of_forall fun _ => Or.inl hχ
      · exact (eventually_ne_nhds hs1).mono fun _ hz => Or.inr hz
    filter_upwards [hnear] with z hz
    exact LFunction_changeLevel hMN χ hz
  have hfac : ∀ p ∈ N.primeFactors, 1 - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
    intro p hp
    apply IsUnit.ne_zero
    apply IsUnit.one_sub_of_norm_lt_one
    rw [norm_mul]
    calc ‖χ p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * ‖(p : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)
      _ < 1 := by
        have h := norm_cpow_neg_le (Nat.prime_of_mem_primeFactors hp) hs
        linarith
  have hdfac : ∀ p ∈ N.primeFactors,
      DifferentiableAt ℂ (fun z : ℂ => 1 - χ p * (p : ℂ) ^ (-z)) s :=
    fun p hp => (hasDerivAt_factor_mul _ (Nat.prime_of_mem_primeFactors hp) s).differentiableAt
  have hχ0 := LFunction_ne_zero_of_one_le_re χ hχs hs
  have hχd := differentiableAt_LFunction χ s hχs.symm
  have hl : deriv (LFunction (changeLevel hMN χ)) s / LFunction (changeLevel hMN χ) s =
      logDeriv (fun z => LFunction χ z *
        ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-z))) s := by
    rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hl, logDeriv_fun_mul s hχ0 (Finset.prod_ne_zero_iff.mpr hfac)
    hχd (DifferentiableAt.fun_finsetProd hdfac), logDeriv_apply (LFunction χ),
    add_sub_cancel_left, logDeriv_fun_prod hfac hdfac]
  have he : (∑ p ∈ N.primeFactors, logDeriv (fun z : ℂ => 1 - χ p * (p : ℂ) ^ (-z)) s) =
      ∑ p ∈ N.primeFactors \ M.primeFactors,
        logDeriv (fun z : ℂ => 1 - χ p * (p : ℂ) ^ (-z)) s := by
    symm
    apply Finset.sum_subset Finset.sdiff_subset
    intro p hp hnot
    have hpM : p ∈ M.primeFactors := by
      by_contra h
      exact hnot (Finset.mem_sdiff.mpr ⟨hp, h⟩)
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hχp : χ (p : ZMod M) = 0 := χ.map_nonunit (fun hu =>
      (ZMod.isUnit_prime_iff_not_dvd hp').mp hu (Nat.dvd_of_mem_primeFactors hpM))
    simp [hχp, logDeriv_apply]
  rw [he]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp =>
    norm_logDeriv_factor_mul_le _ (χ.norm_le_one _)
      (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1) hs)

/-- A modulus-only bound for the correction under a change of level. -/
theorem norm_logDeriv_changeLevel_sub_le {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) {s : ℂ}
    (hs : 1 ≤ s.re) (hχs : χ ≠ 1 ∨ s ≠ 1) :
    ‖deriv (LFunction (changeLevel hMN χ)) s / LFunction (changeLevel hMN χ) s -
      deriv (LFunction χ) s / LFunction χ s‖ ≤ Real.log N := by
  refine (norm_logDeriv_changeLevel_sub_le_sum hMN χ hs hχs).trans ?_
  refine (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset ?_).trans
    (sum_log_primeFactors_le N)
  intro p hp _
  exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)


lemma norm_logDeriv_sub_le (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
      - deriv riemannZeta s / riemannZeta s‖ ≤ Real.log q := by
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have h := norm_logDeriv_changeLevel_sub_le (one_dvd q) (1 : DirichletCharacter ℂ 1) hs.le (.inr hs1)
  simpa only [map_one, LFunction_modOne_eq] using h


theorem neg_re_logDeriv_le : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 → -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (σ + t * I) / LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)).re ≤ (1 / ((σ : ℂ) + t * I - 1)).re + C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C, hC, hZ⟩ := _root_.GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local
  refine ⟨C + 1, by linarith, ?_⟩
  intro q _ σ t hσ1 hσ2
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hsne : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs1
    exact lt_irrefl _ hs1
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hdist : ‖s - (3 / 2 + t * I)‖ ≤ 2 / 3 := by
    have h1 : s - (3 / 2 + t * I) = ((σ - 3 / 2 : ℝ) : ℂ) := by
      rw [hsdef]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  obtain ⟨hfin, hbound⟩ := hZ t s hdist hsne hζ0
  set Z := {w : ℂ | ‖w - (3 / 2 + t * I)‖ ≤ 5 / 6 ∧ w ≠ 1 ∧ riemannZeta w = 0} with hZdef
  set S := ∑ᶠ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w) with hSdef
  have hterm : ∀ w ∈ Z, 0 ≤ ((analyticOrderNatAt riemannZeta w : ℂ) / (s - w)).re := by
    intro w hw
    have hw1 : w.re ≤ 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_lt_re h hw.2.2
    have hpos : 0 ≤ (s - w).re := by rw [Complex.sub_re, hsre]; linarith
    rw [Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hpos) (Complex.normSq_nonneg _)
  have hS : 0 ≤ S.re := by
    rw [hSdef, finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.re_sum]
    exact Finset.sum_nonneg fun w hw => hterm w (hfin.mem_toFinset.mp hw)
  set E := deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - S with hEdef
  have hζ : deriv riemannZeta s / riemannZeta s = E - 1 / (s - 1) + S := by
    rw [hEdef]; ring
  have hE : -E.re ≤ C * Real.log (|t| + 2) :=
    le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm E) hbound)
  set D := deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
    - deriv riemannZeta s / riemannZeta s with hDdef
  have hD : ‖D‖ ≤ Real.log q := norm_logDeriv_sub_le q hs1
  have hDre : -D.re ≤ Real.log q := le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm D) hD)
  have hLsplit : deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
      LFunction (1 : DirichletCharacter ℂ q) s = D + (E - 1 / (s - 1) + S) := by
    rw [hDdef, ← hζ]; ring
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hlt : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith)
  have hlog : Real.log (q * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
    Real.log_mul (by linarith) (by linarith)
  rw [hLsplit, hlog]
  simp only [Complex.add_re, Complex.sub_re]
  nlinarith

open Filter Topology

end GlobalTheory.PrincipalLogDeriv
