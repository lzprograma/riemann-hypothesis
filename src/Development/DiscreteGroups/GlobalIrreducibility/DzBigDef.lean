module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq

namespace DiscreteGroups.sglob.DzType

theorem big_of_le_nV (D : Formalism.BasicNotions.D7) (k : Fin 2) {n : ℕ} (hn : n ≤ D.R.nV) : 16 * n ^ 2 < D.host.g k := by
  have hg : D.host.g k % (D.host.QS * D.host.q * D.host.d) = 1 := D.ntypes.g_cond k
  have hq := D.host.qd_big
  have ht : 0 < D.R.t := D.R.t_odd.pos
  have hr : 1 ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; have := D.R.two_le_m; omega
  have h2 : 2 ≤ D.host.g k := (D.host.g_prime k).two_le
  have hQ0 : 0 < D.host.QS := by
    rcases Nat.eq_zero_or_pos D.host.QS with h | h
    · rw [h] at hg; simp at hg; omega
    · exact h
  have h16 : 16 ≤ D.host.QS :=
    Nat.le_of_dvd hQ0 ((pow_dvd_pow 2 (m := 4) (by have := D.host.two_le_e; omega)).trans D.host.tower_dvd)
  have hdvd : D.host.QS * D.host.q * D.host.d ∣ D.host.g k - 1 := by
    have := Nat.mod_add_div (D.host.g k) (D.host.QS * D.host.q * D.host.d)
    rw [hg] at this
    exact ⟨D.host.g k / (D.host.QS * D.host.q * D.host.d), Nat.sub_eq_of_eq_add' this.symm⟩
  have hle := Nat.le_of_dvd (by omega) hdvd
  have hn' : n ≤ 4 * D.R.t * D.R.r + 1 := by
    unfold Formalism.BasicNotions.Ranks.nV at hn
    nlinarith
  have hq1 : n ≤ D.host.q := by omega
  have hd1 : n ≤ D.host.d := by omega
  have h5 : n * n ≤ D.host.q * D.host.d := Nat.mul_le_mul hq1 hd1
  have h6 : 16 * (D.host.q * D.host.d) ≤ D.host.QS * D.host.q * D.host.d := by
    rw [mul_assoc D.host.QS]
    exact Nat.mul_le_mul_right _ h16
  rw [sq]
  omega

end DiscreteGroups.sglob.DzType
