module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsIsoGmOfMap
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda.Lazard

theorem norm_natCast_eq_one_of_not_dvd {K : Type} [NormedField K] [IsUltrametricDist K] {l m : ℕ}
    (hp : l.Prime) (hl : ‖(l : K)‖ < 1) (hm : ¬ l ∣ m) : ‖(m : K)‖ = 1 := by
  apply GlobalTheory.ConvSer.TowerNorm.norm_natCast_eq_one <;> assumption

theorem not_dvd_choose_pow_mul {l : ℕ} (hp : l.Prime) (m : ℕ) (hm : ¬ l ∣ m) :
    ∀ v : ℕ, ¬ l ∣ (l ^ v * m).choose (l ^ v) := by
  haveI := Fact.mk hp
  intro v
  induction v with
  | zero => simpa using hm
  | succ v ih =>
    have h := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (l ^ (v + 1) * m) (l ^ (v + 1)) l _
    have e1 : l ^ (v + 1) * m = l * (l ^ v * m) := by ring
    have e2 : l ^ (v + 1) = l * l ^ v := by ring
    rw [e1, e2, Nat.mul_mod_right, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hp.pos,
      Nat.mul_div_cancel_left _ hp.pos, Nat.choose_zero_right, one_mul] at h
    rw [e1, e2]
    intro hd
    exact ih ((Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 hd))))

theorem choose_prime_pow_pred {l : ℕ} (hp : l.Prime) (i : ℕ) (hi : 0 < i) :
    ∃ m : ℕ, ¬ l ∣ m ∧ (l ^ i).choose (l ^ (i - 1)) = l * m := by
  have hle : l ^ (i - 1) ≤ l ^ i := Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)
  have h := hp.emultiplicity_choose_prime_pow_add_emultiplicity hle (pow_ne_zero _ hp.ne_zero)
  rw [emultiplicity_pow_self_of_prime hp.prime] at h
  have h1 : emultiplicity l ((l ^ i).choose (l ^ (i - 1))) = ((1 : ℕ) : ℕ∞) := by
    have : ((i : ℕ) : ℕ∞) = ((1 : ℕ) : ℕ∞) + ((i - 1 : ℕ) : ℕ∞) := by
      rw [← Nat.cast_add]; congr 1; omega
    rw [this] at h
    exact WithTop.add_right_cancel (ENat.coe_ne_top _) h
  rw [emultiplicity_eq_coe] at h1
  obtain ⟨⟨m, hm⟩, hn⟩ := h1
  refine ⟨m, ?_, by simpa using hm⟩
  rintro ⟨c, rfl⟩
  apply hn
  exact ⟨c, by rw [hm]; ring⟩

theorem lazard_binomial : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (a : K) (n : ℕ), 2 ≤ n →
    (∀ k, 0 < k → k < n → ‖a * (n.choose k : K)‖ ≤ ‖(l : K)‖) →
    ‖a‖ ≤ ‖(l : K)‖ ∨ (‖a‖ ≤ 1 ∧ ∃ i : ℕ, 0 < i ∧ n = l ^ i) := by
  intro K _ _ _ l hp hl a n hn h
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) l hp.one_lt.ne'
  have hlpos : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.ne_zero)
  by_cases hm1 : m = 1
  · subst hm1
    simp only [mul_one] at h hn ⊢
    have he : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · subst h0; simp at hn
      · exact h0
    refine Or.inr ⟨?_, e, he, rfl⟩
    obtain ⟨c, hc, hch⟩ := choose_prime_pow_pred hp e he
    have hk := h (l ^ (e - 1)) (pow_pos hp.pos _) (Nat.pow_lt_pow_right hp.one_lt (by omega))
    rw [hch, Nat.cast_mul, norm_mul, norm_mul, norm_natCast_eq_one_of_not_dvd hp hl hc, mul_one] at hk
    exact le_of_mul_le_mul_right (by rwa [one_mul]) hlpos
  · left
    have hm0 : m ≠ 0 := by rintro rfl; simp at hn
    have hk := h (l ^ e) (pow_pos hp.pos e)
      (lt_mul_of_one_lt_right (pow_pos hp.pos e) (by omega))
    rwa [norm_mul, norm_natCast_eq_one_of_not_dvd hp hl (not_dvd_choose_pow_mul hp m hm e), mul_one] at hk

end GlobalTheory.Honda.Lazard
