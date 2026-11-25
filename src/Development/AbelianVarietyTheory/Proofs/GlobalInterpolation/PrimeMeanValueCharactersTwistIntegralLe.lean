module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Totient
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultiplicativeLargeSieve
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Algebra.Order.Chebyshev
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralNormSqLp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HybridLargeSieve
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArithmeticLargeSieveOneResidueClassPerPrime, Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BrunTitchmarshExistsConst, Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimeMeanValueCharactersTwistIntegralLe

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArithmeticLargeSieveOneResidueClassPerPrime =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArithmeticLargeSieveOneResidueClassPerPrime", "h": "module\n\npublic import Mathlib.Analysis.SpecialFunctions.Log.Basic\npublic import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic\npublic import Mathlib.Data.Nat.Totient\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultiplicativeLargeSieve\npublic import Mathlib.NumberTheory.Harmonic.Bounds\npublic import Mathlib.Algebra.Order.Chebyshev\n\n"}
section -- clump:auto
@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

private lemma totient_mul_sigma_pow_le_pow_succ (K n : ℕ) (hn : 0 < n) : n.totient * sigma 1 (n ^ K) ≤ n ^ (K + 1) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha =>
    rw [← pow_mul, sigma_one_apply_prime_pow hp, Nat.totient_prime_pow hp ha, mul_assoc]
    have key : (p - 1) * ∑ i ∈ Finset.range (a * K + 1), p ^ i = p ^ (a * K + 1) - 1 := by
      zify [hp.one_le, Nat.one_le_pow _ _ hp.pos]; rw [mul_comm, geom_sum_mul]
    rw [key, ← pow_mul]; refine (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans_eq ?_
    rw [← pow_add]; congr 1; cases a with | zero => omega | succ a => simp; ring
  | zero => omega
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [mul_pow, Nat.totient_mul hab, isMultiplicative_sigma.map_mul_of_coprime (hab.pow K K), mul_pow]
    exact (by ring : _ = (a.totient * sigma 1 (a ^ K)) * (b.totient * sigma 1 (b ^ K))).trans_le (Nat.mul_le_mul (iha ha.pos) (ihb hb.pos))

private lemma sum_inv_le_mul_sum_squarefree_inv_totient (Q q : ℕ) (hq : 1 ≤ q) :
    ∑ n ∈ Finset.Icc 1 Q, (1 : ℝ) / n ≤ ((q : ℝ) / q.totient) *
      ∑ f ∈ (Finset.Icc 1 Q).filter (fun f => Squarefree f ∧ Nat.Coprime f q), (1 : ℝ) / f.totient := by
  set D := (Finset.Icc 1 Q).filter fun f => Squarefree f ∧ Nat.Coprime f q with hD
  set g : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ q), p
  have hsq : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → Squarefree (∏ p ∈ s, p) := fun s hs => by
    rw [Nat.squarefree_iff_prime_squarefree]; intro x hx hxx
    have hmem : ∀ {t}, t ⊆ s → x ∣ ∏ p ∈ t, p → x ∈ t := fun ht hd => by
      obtain ⟨p, hp, hxp⟩ := (Prime.dvd_finsetProd_iff hx.prime _).1 hd; rwa [(Nat.prime_dvd_prime_iff_eq hx (hs p (ht hp))).1 hxp]
    rw [← Finset.mul_prod_erase s (fun p => p) (hmem subset_rfl ((dvd_mul_right x x).trans hxx))] at hxx
    have := hmem (Finset.erase_subset _ _) (Nat.dvd_of_mul_dvd_mul_left hx.pos hxx); simp at this
  have hgdvd : ∀ n, g n ∣ n := fun n => (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd n)
  have hgD : ∀ n ∈ Finset.Icc 1 Q, g n ∈ D := fun n hn => by
    rw [Finset.mem_Icc] at hn
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨Nat.pos_of_dvd_of_pos (hgdvd n) hn.1, (Nat.le_of_dvd hn.1 (hgdvd n)).trans hn.2⟩,
      hsq _ fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1,
      Nat.Coprime.prod_left fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).coprime_iff_not_dvd.2 (Finset.mem_filter.1 hp).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hgD, Finset.mul_sum]; refine Finset.sum_le_sum fun f hf => ?_
  rw [hD, Finset.mem_filter, Finset.mem_Icc] at hf; set N := (f * q) ^ Q with hN
  have hfq0 : f * q ≠ 0 := (Nat.mul_pos hf.1.1 hq).ne'; have hN0 : N ≠ 0 := pow_ne_zero _ hfq0
  have hfib : ∀ n ∈ (Finset.Icc 1 Q).filter (fun n => g n = f), f ∣ n ∧ n ∣ N := fun n hn => by
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    refine ⟨hn.2 ▸ hgdvd n, ((Nat.factorization_le_iff_dvd (by omega) (pow_ne_zero n hfq0)).1 fun p => ?_).trans (pow_dvd_pow _ hn.1.2)⟩
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    by_cases hp : p.Prime ∧ p ∣ n
    · have hpdiv : p ∣ f * q := if hpq : p ∣ q then dvd_mul_of_dvd_right hpq _
        else dvd_mul_of_dvd_left (hn.2 ▸ Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hp.1.mem_primeFactors hp.2 (by omega), hpq⟩)) _
      exact (Nat.factorization_lt p (by omega : n ≠ 0)).le.trans (Nat.le_mul_of_pos_right _ ((hp.1.dvd_iff_one_le_factorization hfq0).1 hpdiv))
    · rw [if hp' : p.Prime then Nat.factorization_eq_zero_of_not_dvd fun hd => hp ⟨hp', hd⟩ else Nat.factorization_eq_zero_of_not_prime _ hp']; exact Nat.zero_le _
  calc ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => g n = f), (1 : ℝ) / n
      = ∑ m ∈ ((Finset.Icc 1 Q).filter (fun n => g n = f)).image (· / f), (1 : ℝ) / (f * m) := by
        rw [Finset.sum_image fun x hx y hy hxy => (Nat.div_left_inj (hfib x hx).1 (hfib y hy).1).1 hxy]
        exact Finset.sum_congr rfl fun n hn => by rw [← Nat.cast_mul, Nat.mul_div_cancel' (hfib n hn).1]
    _ ≤ ∑ m ∈ N.divisors, (1 : ℝ) / (f * m) := Finset.sum_le_sum_of_subset_of_nonneg
        (fun m hm => by obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm; exact Nat.mem_divisors.2 ⟨(Nat.div_dvd_of_dvd (hfib n hn).1).trans (hfib n hn).2, hN0⟩) fun _ _ _ => by positivity
    _ = (1 / f) * ((sigma 1 N : ℝ) / N) := by
        rw [sigma_one_apply, Nat.cast_sum, Finset.sum_div, ← Nat.sum_div_divisors, Finset.mul_sum]; refine Finset.sum_congr rfl fun d hd => ?_
        have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pos_of_mem_divisors hd).ne'
        have hN0' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN0
        rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0]; field_simp
    _ ≤ (q : ℝ) / q.totient * (1 / f.totient) := by
        have := hf.1.1; rw [hN, mul_pow, isMultiplicative_sigma.map_mul_of_coprime (hf.2.2.pow Q Q), one_div_mul_eq_div, div_div, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        exact_mod_cast (by ring : (sigma 1 (f ^ Q) * sigma 1 (q ^ Q)) * (q.totient * f.totient) = (f.totient * sigma 1 (f ^ Q)) * (q.totient * sigma 1 (q ^ Q))).trans_le
          ((Nat.mul_le_mul (totient_mul_sigma_pow_le_pow_succ Q f hf.1.1) (totient_mul_sigma_pow_le_pow_succ Q q hq)).trans_eq (by ring))

private lemma norm_sum_sq_le_pred_mul_of_avoids_class (p : ℕ) (hp : p.Prime) (c : ℕ) (S : Finset ℕ) (b : ℕ → ℂ) (hS : ∀ n ∈ S, ¬ n ≡ c [MOD p]) :
    ‖∑ n ∈ S, b n‖ ^ 2 ≤ (p - 1 : ℝ) * ∑ a ∈ (Finset.range p).erase 0, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / p)‖ ^ 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  set ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  set B : ZMod p → ℂ := fun r => ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod p) = r), b n
  have hconj : ∀ u : ZMod p, starRingEnd ℂ (ψ u) = ψ (-u) := fun u => by
    dsimp only [ψ]; rw [← ZMod.natCast_zmod_val u, ← Int.cast_natCast, ZMod.stdAddChar_coe, ← Complex.exp_conj, ← Int.cast_neg, ZMod.stdAddChar_coe]
    congr 1; push_cast; simp only [map_mul, map_div₀, conj_ofReal, conj_I, map_natCast, map_ofNat]; ring
  have hgroup : ∀ a : ℕ, ∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / p) = ∑ r : ZMod p, B r * ψ (r * a) := fun a => by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun n : ℕ => (n : ZMod p)) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun r _ => ?_; dsimp only [B, ψ]; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun n hn => ?_
    have hcoe := ZMod.stdAddChar_coe (N := p) ((n * a : ℕ) : ℤ); push_cast at hcoe; rw [← (Finset.mem_filter.1 hn).2, hcoe]; congr 2; ring
  have hpar : ∑ a ∈ Finset.range p, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / p)‖ ^ 2 = p * ∑ r : ZMod p, ‖B r‖ ^ 2 := by
    simp_rw [hgroup]
    rw [show ∑ a ∈ Finset.range p, ‖∑ r : ZMod p, B r * ψ (r * a)‖ ^ 2 = ∑ a : ZMod p, ‖∑ r : ZMod p, B r * ψ (r * a)‖ ^ 2 from
      Finset.sum_nbij' (fun a => (a : ZMod p)) ZMod.val (fun _ _ => Finset.mem_univ _) (fun a _ => Finset.mem_range.2 (ZMod.val_lt a))
        (fun a ha => ZMod.val_cast_of_lt (Finset.mem_range.1 ha)) (fun _ _ => ZMod.natCast_zmod_val _) fun _ _ => rfl]
    apply Complex.ofReal_injective; push_cast; simp_rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, map_mul, hconj]
    rw [Finset.sum_comm, Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_; rw [Finset.sum_comm]
    have horth : ∀ s : ZMod p, ∑ a : ZMod p, B r * ψ (r * a) * (starRingEnd ℂ (B s) * ψ (-(s * a))) =
        if r = s then p * (B r * starRingEnd ℂ (B s)) else 0 := fun s => by
      have hmul : ∀ a : ZMod p, B r * ψ (r * a) * (starRingEnd ℂ (B s) * ψ (-(s * a))) = B r * starRingEnd ℂ (B s) * ψ (a * (r - s)) := fun a => by
        calc B r * ψ (r * a) * (starRingEnd ℂ (B s) * ψ (-(s * a))) = B r * starRingEnd ℂ (B s) * (ψ (r * a) * ψ (-(s * a))) := by ring
          _ = B r * starRingEnd ℂ (B s) * ψ (a * (r - s)) := by rw [← AddChar.map_add_eq_mul]; congr 2; ring
      simp_rw [hmul, ← Finset.mul_sum]; rw [AddChar.sum_mulShift (r - s) (ZMod.isPrimitive_stdAddChar p), ZMod.card]
      by_cases hrs : r = s; · subst hrs; simp [mul_comm]
      · simp [sub_eq_zero, hrs]
    simp [horth, Complex.mul_conj']
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hp.pos)] at hpar
  simp only [Nat.cast_zero, mul_zero, zero_div, Complex.exp_zero, mul_one] at hpar
  have hc : B c = 0 := by dsimp only [B]; rw [Finset.filter_false_of_mem fun n hn h => hS n hn ((ZMod.natCast_eq_natCast_iff n c p).1 h)]; simp
  have hcs : ‖∑ n ∈ S, b n‖ ^ 2 ≤ (p - 1 : ℝ) * ∑ r : ZMod p, ‖B r‖ ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun n : ℕ => (n : ZMod p)) (fun _ _ => Finset.mem_univ _) b, ← Finset.sum_erase _ hc]
    calc _ ≤ (∑ r ∈ Finset.univ.erase (c : ZMod p), ‖B r‖) ^ 2 := by gcongr; exact norm_sum_le _ _
      _ ≤ ((Finset.univ.erase (c : ZMod p)).card : ℝ) * ∑ r ∈ Finset.univ.erase (c : ZMod p), ‖B r‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (p - 1 : ℝ) * ∑ r : ZMod p, ‖B r‖ ^ 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card, Nat.cast_sub hp.one_le, Nat.cast_one]
          gcongr; exact sub_nonneg.2 (by exact_mod_cast hp.one_le); exact Finset.erase_subset _ _
  rw [← sub_nonneg]
  calc (0 : ℝ) ≤ p * ((p - 1) * ∑ r : ZMod p, ‖B r‖ ^ 2 - ‖∑ n ∈ S, b n‖ ^ 2) := mul_nonneg (Nat.cast_nonneg p) (sub_nonneg.2 hcs)
    _ = (p - 1) * (p * ∑ r : ZMod p, ‖B r‖ ^ 2) - p * ‖∑ n ∈ S, b n‖ ^ 2 := by ring
    _ = _ := by rw [← hpar]; ring

private lemma norm_sum_sq_le_totient_mul_of_avoids_classes (S : Finset ℕ) (d : ℕ) (hd : 0 < d)
    (hsq : Squarefree d) (hcl : ∀ p : ℕ, p.Prime → p ∣ d → ∃ c : ℕ, ∀ n ∈ S, ¬ n ≡ c [MOD p]) (b : ℕ → ℂ) :
    ‖∑ n ∈ S, b n‖ ^ 2 ≤ (d.totient : ℝ) * ∑ a ∈ (Finset.range d).filter d.Coprime, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / d)‖ ^ 2 := by
  induction d using Nat.strong_induction_on generalizing b with
  | _ d ih =>
  by_cases h1 : d = 1
  · subst h1; rw [show (Finset.range 1).filter (Nat.Coprime 1) = {0} by decide]; simp
  obtain ⟨p, hp, d₁, rfl⟩ := Nat.exists_prime_and_dvd h1; rw [mul_comm p d₁] at hsq hcl ⊢
  have hd₁ : 0 < d₁ := Nat.pos_of_ne_zero fun h => by subst h; simp at hd
  have hpd₁ : ¬ p ∣ d₁ := fun h => hp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p (Nat.mul_dvd_mul h dvd_rfl)))
  have hcop : Nat.Coprime d₁ p := (hp.coprime_iff_not_dvd.2 hpd₁).symm
  obtain ⟨c, hc⟩ := hcl p hp (dvd_mul_left _ _)
  have hd' : (d₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd₁.ne'; have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.pos.ne'
  have hmod : ∀ u v m, Nat.Coprime u (m % (u * v)) ↔ Nat.Coprime u m := fun u v m => by
    have hm : m % (u * v) + v * (m / (u * v)) * u = m := by
      have := Nat.mod_add_div m (u * v); linarith [mul_comm u v, mul_assoc u v (m / (u * v)), mul_comm (v * (m / (u * v))) u]
    conv_rhs => rw [← hm]
    exact (Nat.coprime_add_mul_right_right _ _ _).symm
  let R := ((Finset.range d₁).filter d₁.Coprime) ×ˢ ((Finset.range p).filter p.Coprime)
  have hmaps : ∀ x ∈ R, (x.1 * p + x.2 * d₁) % (d₁ * p) ∈ (Finset.range (d₁ * p)).filter (d₁ * p).Coprime := fun x hx => by
    simp only [R, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx ⊢
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hd₁ hp.pos), Nat.Coprime.mul_left ?_ ?_⟩
    · rw [hmod, Nat.coprime_add_mul_right_right, Nat.coprime_mul_iff_right]; exact ⟨hx.1.2, hcop⟩
    · rw [mul_comm d₁ p, hmod, add_comm, Nat.coprime_add_mul_right_right, Nat.coprime_mul_iff_right]; exact ⟨hx.2.2, hcop.symm⟩
  have hinj : ∀ x ∈ R, ∀ y ∈ R, (x.1 * p + x.2 * d₁) % (d₁ * p) = (y.1 * p + y.2 * d₁) % (d₁ * p) → x = y := fun x hx y hy hxy => by
    simp only [R, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx hy
    have hmod' : x.1 * p + x.2 * d₁ ≡ y.1 * p + y.2 * d₁ [MOD d₁ * p] := hxy
    have e1 := Nat.ModEq.cancel_right_of_coprime hcop (by simpa [Nat.ModEq, Nat.add_mul_mod_self_right] using hmod'.of_mul_right p)
    have e2 := Nat.ModEq.cancel_right_of_coprime hcop.symm (by simpa [Nat.ModEq, Nat.add_mul_mod_self_right] using hmod'.of_mul_left d₁)
    exact Prod.ext (by rw [Nat.ModEq, Nat.mod_eq_of_lt hx.1.1, Nat.mod_eq_of_lt hy.1.1] at e1; exact e1)
      (by rw [Nat.ModEq, Nat.mod_eq_of_lt hx.2.1, Nat.mod_eq_of_lt hy.2.1] at e2; exact e2)
  have hbij : ∑ a ∈ (Finset.range (d₁ * p)).filter (d₁ * p).Coprime, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / ↑(d₁ * p))‖ ^ 2 =
      ∑ a₁ ∈ (Finset.range d₁).filter d₁.Coprime, ∑ a₂ ∈ (Finset.range p).filter p.Coprime,
        ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * ↑(a₁ * p + a₂ * d₁) / ↑(d₁ * p))‖ ^ 2 := by
    rw [← Finset.sum_product']; refine (Finset.sum_nbij _ hmaps hinj (fun z hz => ?_) fun x _ => ?_).symm
    · obtain ⟨x, hx, hxz⟩ := Finset.surj_on_of_inj_on_of_card_le _ hmaps (fun x y hx hy => hinj x hx y hy)
        (le_of_eq (by simp only [R]; rw [Finset.card_product, ← Nat.totient_eq_card_coprime, ← Nat.totient_eq_card_coprime, ← Nat.totient_eq_card_coprime, Nat.totient_mul hcop])) z hz
      exact ⟨x, hx, hxz.symm⟩
    · congr 2; refine Finset.sum_congr rfl fun n _ => ?_
      have hm : ((x.1 * p + x.2 * d₁ : ℕ) : ℂ) = (d₁ * p : ℕ) * ((x.1 * p + x.2 * d₁) / (d₁ * p) : ℕ) + ((x.1 * p + x.2 * d₁) % (d₁ * p) : ℕ) := by
        exact_mod_cast (Nat.div_add_mod (x.1 * p + x.2 * d₁) (d₁ * p)).symm
      generalize (x.1 * p + x.2 * d₁) / (d₁ * p) = k at hm; congr 1
      exact Complex.exp_eq_exp_iff_exists_int.2 ⟨(n * k : ℕ), by rw [hm]; push_cast; field_simp; ring⟩
  have hcrt : ∀ a₁ a₂ n : ℕ, cexp (2 * ↑Real.pi * I * n * ↑(a₁ * p + a₂ * d₁) / ↑(d₁ * p)) =
      cexp (2 * ↑Real.pi * I * n * a₁ / d₁) * cexp (2 * ↑Real.pi * I * n * a₂ / p) := fun _ _ _ => by rw [← Complex.exp_add]; congr 1; push_cast; field_simp
  have herase : (Finset.range p).filter p.Coprime = (Finset.range p).erase 0 := by
    ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, hp.coprime_iff_not_dvd]
    exact ⟨fun ⟨h1, h2⟩ => ⟨by rintro rfl; exact h2 (dvd_zero p), h1⟩, fun ⟨h0, h1⟩ => ⟨h1, fun hd => h0 (Nat.eq_zero_of_dvd_of_lt hd h1)⟩⟩
  rw [hbij]; simp_rw [hcrt, herase, Nat.totient_mul hcop, Nat.totient_prime hp]
  calc ‖∑ n ∈ S, b n‖ ^ 2 ≤ (d₁.totient : ℝ) * ∑ a₁ ∈ (Finset.range d₁).filter d₁.Coprime, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a₁ / d₁)‖ ^ 2 :=
        ih d₁ (by rw [mul_comm]; exact lt_mul_of_one_lt_right hd₁ hp.one_lt) hd₁ (hsq.squarefree_of_dvd (dvd_mul_right _ _)) (fun q hq hqd => hcl q hq (dvd_mul_of_dvd_left hqd _)) b
    _ ≤ (d₁.totient : ℝ) * ∑ a₁ ∈ (Finset.range d₁).filter d₁.Coprime, (p - 1 : ℝ) * ∑ a₂ ∈ (Finset.range p).erase 0,
          ‖∑ n ∈ S, b n * (cexp (2 * ↑Real.pi * I * n * a₁ / d₁) * cexp (2 * ↑Real.pi * I * n * a₂ / p))‖ ^ 2 := by
        gcongr with a₁ _; simpa only [mul_assoc] using norm_sum_sq_le_pred_mul_of_avoids_class p hp c S (fun n => b n * cexp (2 * ↑Real.pi * I * n * a₁ / d₁)) hc
    _ = _ := by rw [← Finset.mul_sum]; push_cast [Nat.cast_sub hp.one_le]; ring

theorem _root_.GlobalTheory.arithmetic_large_sieve_one_class : ∀ (M N Q q : ℕ) (S : Finset ℕ), 1 ≤ Q → 1 ≤ q → S ⊆ Finset.Ioc M (M + N) →
    (∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q → ∃ c : ℕ, ∀ n ∈ S, ¬ n ≡ c [MOD p]) →
    (S.card : ℝ) * ((q.totient : ℝ) / q * Real.log Q) ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N := by
  intro M N Q q S hQ hq hS hcl
  set D := (Finset.Icc 1 Q).filter fun f => Squarefree f ∧ Nat.Coprime f q with hD
  set Z : ℝ := (S.card : ℝ) with hZ
  have hZ0 : 0 ≤ Z := Nat.cast_nonneg _
  rcases hZ0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; positivity
  have hL : (q.totient : ℝ) / q * Real.log Q ≤ ∑ d ∈ D, (1 : ℝ) / d.totient := by
    have h1 := log_add_one_le_harmonic Q; rw [harmonic_eq_sum_Icc] at h1; push_cast at h1
    calc (q.totient : ℝ) / q * Real.log Q ≤ (q.totient : ℝ) / q * (((q : ℝ) / q.totient) * ∑ d ∈ D, (1 : ℝ) / d.totient) := by
          gcongr; exact ((Real.log_le_log (by exact_mod_cast hQ) (by linarith : (Q : ℝ) ≤ Q + 1)).trans (by simpa [one_div] using h1)).trans (sum_inv_le_mul_sum_squarefree_inv_totient Q q hq)
      _ = _ := by rw [← mul_assoc, show (q.totient : ℝ) / q * (q / q.totient) = 1 by field_simp, one_mul]
  set U : ℕ → ℝ := fun d => ∑ a ∈ (Finset.range d).filter d.Coprime, ‖∑ n ∈ S, (1 : ℂ) * cexp (2 * ↑Real.pi * I * n * a / d)‖ ^ 2
  have hmont : ∀ d ∈ D, Z ^ 2 * ((1 : ℝ) / d.totient) ≤ U d := fun d hd => by
    rw [hD, Finset.mem_filter, Finset.mem_Icc] at hd
    have h := norm_sum_sq_le_totient_mul_of_avoids_classes S d hd.1.1 hd.2.1
      (fun p hp hpd => hcl p hp ((Nat.le_of_dvd hd.1.1 hpd).trans hd.1.2) fun hpq => hp.coprime_iff_not_dvd.1 (hd.2.2.coprime_dvd_left hpd) hpq) (fun _ => 1)
    have hφd : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 hd.1.1
    rw [mul_one_div, div_le_iff₀ hφd, mul_comm]; simpa [hZ, U] using h
  have hls : ∑ d ∈ D, U d ≤ ((Q : ℝ) ^ 2 + 2 * Real.pi * N) * Z := by
    set P := D.sigma fun d => (Finset.range d).filter d.Coprime with hP
    set T : Finset ℝ := P.image fun x => (x.2 : ℝ) / x.1 with hT
    have hmemP : ∀ x ∈ P, 0 < x.1 ∧ x.1 ≤ Q ∧ x.2 < x.1 ∧ Nat.Coprime x.2 x.1 := fun x hx => by
      rw [hP, Finset.mem_sigma, hD, Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hx; exact ⟨hx.1.1.1, hx.1.1.2, hx.2.1, hx.2.2.symm⟩
    have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ => (x.2 : ℝ) / x.1) P := fun x hx y hy hxy => by
      obtain ⟨e1, e2⟩ := MultSieve.reduced_inj (hmemP x hx).1 (hmemP y hy).1 (hmemP x hx).2.2.2 (hmemP y hy).2.2.2 hxy; exact Sigma.ext e1 (heq_of_eq e2)
    calc ∑ d ∈ D, U d = ∑ x ∈ T, ‖∑ n ∈ Finset.Ioc M (M + N), (if n ∈ S then (1 : ℂ) else 0) * cexp (2 * ↑Real.pi * I * ↑n * ↑x)‖ ^ 2 := by
          rw [hT, Finset.sum_image hinj, hP, Finset.sum_sigma]; refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => ?_
          simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS]
          congr 2; exact Finset.sum_congr rfl fun n _ => by congr 1; push_cast; ring
      _ ≤ (1 / (1 / (Q : ℝ) ^ 2) + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖(if n ∈ S then (1 : ℂ) else 0)‖ ^ 2 :=
          additive_large_sieve M N _ T _ (by positivity) (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by exact_mod_cast hQ)) fun x hx y hy hxy k => by
            obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
            exact MultSieve.farey_spaced Q u.1 v.1 u.2 v.2 (hmemP u hu).2.1 (hmemP v hv).2.1 (hmemP u hu).2.2.1 (hmemP v hv).2.2.1 hxy k
      _ = ((Q : ℝ) ^ 2 + 2 * Real.pi * N) * Z := by
          rw [one_div_one_div]; congr 1
          have hpt : ∀ n, ‖(if n ∈ S then (1 : ℂ) else 0)‖ ^ 2 = if n ∈ S then (1 : ℝ) else 0 := fun n => by split_ifs <;> simp
          simp_rw [hpt, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS]; simp [hZ]
  have hbig : Z * (Z * ∑ d ∈ D, (1 : ℝ) / d.totient) ≤ Z * ((Q : ℝ) ^ 2 + 2 * Real.pi * N) := by
    calc _ = ∑ d ∈ D, Z ^ 2 * ((1 : ℝ) / d.totient) := by rw [← Finset.mul_sum]; ring
      _ ≤ _ := ((Finset.sum_le_sum hmont).trans hls).trans_eq (mul_comm _ _)
  exact (mul_le_mul_of_nonneg_left hL hZ0).trans (le_of_mul_le_mul_left hbig hpos)

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArithmeticLargeSieveOneResidueClassPerPrime =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BrunTitchmarshExistsConst =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BrunTitchmarshExistsConst", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc\npublic import Mathlib.Analysis.SpecialFunctions.Log.Basic\npublic import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic\npublic import Mathlib.Data.Nat.Totient\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArithmeticLargeSieveOneResidueClassPerPrime\npublic import Mathlib.Analysis.Real.Pi.Bounds\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.GroupTheory.Nilpotent\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

theorem exists_dvd_mul_add_of_prime (l q r : ℕ) (hl : l.Prime) (hq : ¬ l ∣ q) : ∃ c : ℕ, l ∣ q * c + r := by
  haveI := Fact.mk hl
  have hq' : (q : ZMod l) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q l).1 h)
  refine ⟨(-(r : ZMod l) * (q : ZMod l)⁻¹).val, (ZMod.natCast_eq_zero_iff _ l).1 ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  field_simp
  ring

theorem card_large_primes_class_le (q a Q M N : ℕ) (P : Finset ℕ) (hq : 1 ≤ q) (hQ : 1 ≤ Q)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≡ a [MOD q] ∧ Q < p ∧ q * M ≤ p ∧ p < q * (M + N)) :
    (P.card : ℝ) * ((q.totient : ℝ) / q * Real.log Q) ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N := by
  have hdec : ∀ p ∈ P, p = q * (p / q) + a % q := fun p hp => by
    have h : p % q = a % q := (hP p hp).2.1
    rw [← h, Nat.div_add_mod]
  have hinj : Set.InjOn (fun p => p / q + 1) (P : Set ℕ) := by
    intro p hp p' hp' h
    have h' : p / q = p' / q := by simpa using h
    rw [hdec p hp, hdec p' hp', h']
  have key := _root_.GlobalTheory.arithmetic_large_sieve_one_class M N Q q (P.image fun p => p / q + 1) hQ hq ?_ ?_
  · rwa [Finset.card_image_of_injOn hinj] at key
  · intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨-, -, -, h1, h2⟩ := hP p hp
    have h3 : M ≤ p / q := (Nat.le_div_iff_mul_le hq).2 (by rwa [mul_comm])
    have h4 : p / q < M + N := (Nat.div_lt_iff_lt_mul hq).2 (by rwa [mul_comm])
    exact Finset.mem_Ioc.2 ⟨by omega, by omega⟩
  · intro l hl hlQ hlq
    obtain ⟨c, hc⟩ := exists_dvd_mul_add_of_prime l q (a % q) hl hlq
    refine ⟨c + 1, fun n hn h => ?_⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hn
    have h1 : p / q ≡ c [MOD l] := Nat.ModEq.add_right_cancel' 1 h
    have h2 : q * (p / q) + a % q ≡ q * c + a % q [MOD l] := (h1.mul_left q).add_right _
    rw [← hdec p hp] at h2
    have h3 : l ∣ p := (Nat.modEq_zero_iff_dvd).1 (h2.trans ((Nat.modEq_zero_iff_dvd).2 hc))
    have h4 := (Nat.prime_dvd_prime_iff_eq hl (hP p hp).1).1 h3
    have := (hP p hp).2.2.1
    omega

theorem brun_titchmarsh_const : ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ) (x y : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ x → 2 * (q : ℝ) ≤ y → (((primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q])).card : ℝ) ≤ C * y / (q.totient * Real.log (y / q)) := by
  refine ⟨48, by norm_num, fun q a x y hq _ hx hy => ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = y / q := ⟨_, rfl⟩
  have hyz : y = q * z := by rw [hz]; field_simp
  have hz2 : 2 ≤ z := by rw [hz, le_div_iff₀ hq0]; exact hy
  rw [← hz]
  have hfl : 2 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz2)
  have hflz : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hzfl : z < ⌊z⌋₊ + 1 := Nat.lt_floor_add_one z
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt ⌊z⌋₊ := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs, Nat.le_sqrt]; omega
  have hs2 : s * s ≤ ⌊z⌋₊ := hs ▸ Nat.sqrt_le _
  have hs3 : ⌊z⌋₊ < (s + 1) * (s + 1) := hs ▸ Nat.lt_succ_sqrt _
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = s + 1 := ⟨_, rfl⟩
  have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast (by omega : 2 ≤ Q)
  have hQz : (Q : ℝ) ^ 2 ≤ 4 * z := by
    have : Q ^ 2 ≤ 4 * ⌊z⌋₊ := by
      rw [hQ]
      calc (s + 1) ^ 2 ≤ (2 * s) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 4 * (s * s) := by ring
        _ ≤ 4 * ⌊z⌋₊ := Nat.mul_le_mul_left 4 hs2
    have : (Q : ℝ) ^ 2 ≤ 4 * ⌊z⌋₊ := by exact_mod_cast this
    linarith
  have hzQ : z ≤ (Q : ℝ) ^ 2 := by
    have : ⌊z⌋₊ + 1 ≤ Q ^ 2 := by rw [hQ, sq]; omega
    have : (⌊z⌋₊ : ℝ) + 1 ≤ (Q : ℝ) ^ 2 := by exact_mod_cast this
    linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlog : Real.log z ≤ 2 * Real.log Q := by
    have := Real.log_le_log (by linarith) hzQ
    rw [Real.log_pow] at this
    exact_mod_cast this
  have hlQ : Real.log Q ≤ Q := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < Q)
    linarith
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  set P := (primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q]) with hP
  have hbig := card_large_primes_class_le q a Q (⌊x⌋₊ / q) (⌊z⌋₊ + 2) (P.filter fun p => Q < p) hq (by omega) (by
    intro p hp
    simp only [hP, primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
    refine ⟨h3, h4, h5, (Nat.mul_div_le _ _).trans h1.le, ?_⟩
    have h6 : (p : ℝ) ≤ x + y := (Nat.le_floor_iff (by linarith)).1 h2
    have h7 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    have h8 : ⌊x⌋₊ + 1 ≤ q * (⌊x⌋₊ / q + 1) := Nat.lt_mul_div_succ _ hq
    have h9 : (⌊x⌋₊ : ℝ) + 1 ≤ q * (((⌊x⌋₊ / q : ℕ) : ℝ) + 1) := by exact_mod_cast h8
    have hy1 : y < q * ((⌊z⌋₊ : ℝ) + 1) := by rw [hyz]; exact mul_lt_mul_of_pos_left hzfl hq0
    have h10 : (p : ℝ) < q * (((⌊x⌋₊ / q : ℕ) : ℝ) + (⌊z⌋₊ + 2)) := by linarith
    exact_mod_cast h10)
  have hsmall : (P.filter fun p => ¬ Q < p).card ≤ Q := by
    calc _ ≤ (Finset.Icc 1 Q).card := Finset.card_le_card fun p hp => by
            simp only [hP, primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
            exact Finset.mem_Icc.2 ⟨hp.1.1.2.one_le, by omega⟩
      _ = Q := by simp
  have hsum := Finset.card_filter_add_card_filter_not (s := P) (fun p => Q < p)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((P.filter fun p => Q < p).card : ℝ) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ Nat.cast_nonneg _
  have hcard : (P.card : ℝ) ≤ B + Q := by
    rw [hB]; exact_mod_cast (by omega)
  rw [← hB] at hbig
  push_cast at hbig
  have hpi := Real.pi_lt_four
  have hpi0 := Real.pi_pos
  have h1 : B * ((q.totient : ℝ) / q * Real.log Q) ≤ 20 * z := by
    have hpi2 : 2 * Real.pi * ((⌊z⌋₊ : ℝ) + 2) ≤ 2 * 4 * (2 * z) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
    linarith
  have h2 : B * (q.totient * Real.log Q) ≤ 20 * y := by
    have := mul_le_mul_of_nonneg_left h1 hq0.le
    rw [hyz]
    calc _ = q * (B * ((q.totient : ℝ) / q * Real.log Q)) := by field_simp
      _ ≤ _ := by linarith
  have h3 : B * (q.totient * Real.log z) ≤ 40 * y := by
    have := mul_le_mul_of_nonneg_left hlog (mul_nonneg hB0 hφ0.le)
    linarith
  have h4 : (Q : ℝ) * Real.log z ≤ 8 * z := by
    have hq1 : (Q : ℝ) * Real.log z ≤ Q * (2 * Q) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have h5 : (Q : ℝ) * (q.totient * Real.log z) ≤ 8 * y := by
    have : (q.totient : ℝ) * (Q * Real.log z) ≤ q * (8 * z) :=
      mul_le_mul hφq h4 (by positivity) hq0.le
    rw [hyz]; linarith
  rw [le_div_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ q.totient * Real.log z)
  linarith

end GlobalTheory.Lin
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BrunTitchmarshExistsConst =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimeMeanValueCharactersTwistIntegralLe =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimeMeanValueCharactersTwistIntegralLe", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc\npublic import Mathlib.NumberTheory.DirichletCharacter.Orthogonality\npublic import Mathlib.RingTheory.SimpleRing.Principal\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BrunTitchmarshExistsConst\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralNormSqLp\nimport Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HybridLargeSieve\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.PrimeMeanValue

theorem conj_char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {u : ZMod q} (hu : IsUnit u) :
    (starRingEnd ℂ) (χ u) = χ u⁻¹ := by
  have h1 : χ u * χ u⁻¹ = 1 := by rw [← map_mul, ZMod.mul_inv_of_unit u hu, map_one]
  have h2 : ‖χ u‖ = 1 := by
    obtain ⟨v, rfl⟩ := hu
    exact χ.unit_norm_eq_one v
  have h3 : χ u * (starRingEnd ℂ) (χ u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h2]; simp
  have h0 : χ u ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact mul_left_cancel₀ h0 (h3.trans h1.symm)

theorem orth (q : ℕ) [NeZero q] (S : Finset ℕ) (a : ℕ → ℂ) (hS : ∀ n ∈ S, Nat.Coprime n q) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 ≤
      ∑ n ∈ S, (q.totient : ℝ) * ((S.filter (fun m => m ≡ n [MOD q])).card : ℝ) * ‖a n‖ ^ 2 := by
  have e1 : ((∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (a n) * a m *
        (if (n : ZMod q) = (m : ZMod q) then (q.totient : ℂ) else 0) := by
    push_cast
    have : ∀ χ : DirichletCharacter ℂ q, ((‖∑ n ∈ S, a n * χ (n : ZMod q)‖ : ℝ) : ℂ) ^ 2 =
        ∑ n ∈ S, ∑ m ∈ S, (starRingEnd ℂ) (a n) * a m * (χ (n : ZMod q)⁻¹ * χ (m : ZMod q)) := by
      intro χ

      rw [← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, conj_char χ ((ZMod.isUnit_iff_coprime n q).2 (hS n hn))]
      ring
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.mul_sum, DirichletCharacter.sum_char_inv_mul_char_eq ℂ
      ((ZMod.isUnit_iff_coprime n q).2 (hS n hn))]
  set g : ℕ → ℕ → ℝ := fun n m => if (n : ZMod q) = (m : ZMod q) then (q.totient : ℝ) else 0
    with hg
  have hsym : ∀ n m, g n m = g m n := fun n m => by simp only [hg, eq_comm]
  have hg0 : ∀ n m, 0 ≤ g n m := fun n m => by simp only [hg]; split_ifs <;> positivity
  have e2 : ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 ≤
      ∑ n ∈ S, ∑ m ∈ S, (‖a n‖ ^ 2 * g n m / 2 + ‖a m‖ ^ 2 * g n m / 2) := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs, ← Complex.norm_real, e1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    have : ‖(if (n : ZMod q) = (m : ZMod q) then (q.totient : ℂ) else 0)‖ = g n m := by
      simp only [hg]; split_ifs <;> simp
    rw [norm_mul, norm_mul, this, Complex.norm_conj]
    have := hg0 n m
    nlinarith [mul_nonneg this (sq_nonneg (‖a n‖ - ‖a m‖))]
  refine e2.trans (le_of_eq ?_)
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun n m => ‖a m‖ ^ 2 * g n m / 2), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hsym n m]
  simp only [hg, ZMod.natCast_eq_natCast_iff]
  split_ifs <;> ring

theorem mem_primesIoc {x y : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ primesIoc x y ↔ x < p ∧ (p : ℝ) ≤ y ∧ p.Prime := by
  rw [primesIoc, Finset.mem_filter, Finset.mem_Ioc, Nat.floor_lt hx]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, (Nat.le_floor_iff' h3.ne_zero).1 h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, Nat.le_floor h2⟩, h3⟩

theorem window (C : ℝ) (hC : 0 < C)
    (hB : ∀ (q a : ℕ) (x y : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ x → 2 * (q : ℝ) ≤ y →
      (((primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q])).card : ℝ) ≤
        C * y / (q.totient * Real.log (y / q)))
    (q : ℕ) [NeZero q] (T N x : ℝ) (a : ℕ → ℂ) (S : Finset ℕ) (hT : 1 ≤ T)
    (hN : (2 * q * T) ^ 2 ≤ N) (hx : 0 < x)
    (hS : ∀ n ∈ S, n.Prime ∧ N < n ∧ x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, a n * χ (n : ZMod q)‖ ^ 2 ≤
      ∑ n ∈ S, 4 * C * n / (T * Real.log n) * ‖a n‖ ^ 2 := by
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hT0 : 0 < T := by linarith
  have hδ : 0 ≤ 1 / T := by positivity
  have hqT : (q : ℝ) ≤ q * T := le_mul_of_one_le_right (by positivity) hT
  have hcop : ∀ n ∈ S, Nat.Coprime n q := fun n hn => by
    obtain ⟨hp, h1, -, -⟩ := hS n hn
    have : (q : ℝ) < n := by
      have h2 : (1 : ℝ) ≤ 2 * q * T := by linarith
      have := le_self_pow₀ h2 (show 2 ≠ 0 by norm_num)
      linarith
    have hlt : q < n := by exact_mod_cast this
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hq hlt)
  have e3 := Real.abs_exp_sub_one_le (x := 1 / T)
    (by rw [abs_of_nonneg hδ, div_le_one hT0]; exact hT)
  rw [abs_of_nonneg hδ] at e3
  have e4 : Real.exp (1 / T) - 1 ≤ 2 * (1 / T) := (le_abs_self _).trans e3
  have e5 : x * Real.exp (1 / T) ≤ x + 2 * x / T := by
    have := mul_le_mul_of_nonneg_left e4 hx.le
    have e : x * (2 * (1 / T)) = 2 * x / T := by ring
    linarith
  have e6 : 2 * x / T ≤ 2 * x := div_le_self (by positivity) hT
  refine (orth q S a hcop).trans (Finset.sum_le_sum fun n hn => ?_)
  obtain ⟨hp, h1, h2, h3⟩ := hS n hn
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hn3 : (n : ℝ) ≤ 3 * x := by linarith
  have hY : 2 * (q : ℝ) ≤ 2 * x / T := by
    rw [le_div_iff₀ hT0]
    have h2 : (2 : ℝ) * (2 * q * T) ≤ (2 * q * T) ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hb := hB q n x (2 * x / T) hq (hcop n hn) hx.le hY
  have hsub : S.filter (fun m => m ≡ n [MOD q]) ⊆
      (primesIoc x (x + 2 * x / T)).filter (fun p => p ≡ n [MOD q]) := by
    refine Finset.filter_subset_filter _ fun m hm => ?_
    obtain ⟨hp', -, h2', h3'⟩ := hS m hm
    exact (mem_primesIoc hx.le).2 ⟨h2', h3'.trans e5, hp'⟩
  have hc : ((S.filter (fun m => m ≡ n [MOD q])).card : ℝ) ≤
      (((primesIoc x (x + 2 * x / T)).filter (fun p => p ≡ n [MOD q])).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hp.one_lt
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hsq : (n : ℝ) ≤ (2 * x / T / q) ^ 2 := by
    rw [div_div, div_pow, le_div_iff₀ (by positivity)]
    have h4 : (T * q) ^ 2 ≤ 3 * x / 4 := by
      have heq : (2 * (q : ℝ) * T) ^ 2 = 4 * (T * q) ^ 2 := by ring
      linarith
    calc (n : ℝ) * (T * q) ^ 2 ≤ (3 * x) * (3 * x / 4) := by gcongr
      _ ≤ (2 * x) ^ 2 := by
        have heq : (2 * x) ^ 2 - 3 * x * (3 * x / 4) = 7 / 4 * x ^ 2 := by ring
        linarith [sq_nonneg x]
  have hl : Real.log n / 2 ≤ Real.log (2 * x / T / q) := by
    have := Real.log_le_log (by linarith) hsq
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  calc (q.totient : ℝ) * ((S.filter (fun m => m ≡ n [MOD q])).card : ℝ)
      ≤ q.totient * (C * (2 * x / T) / (q.totient * Real.log (2 * x / T / q))) :=
        mul_le_mul_of_nonneg_left (hc.trans hb) hφ.le
    _ ≤ q.totient * (C * (2 * n / T) / (q.totient * (Real.log n / 2))) := by gcongr
    _ = 4 * C * n / (T * Real.log n) := by field_simp; ring

theorem prime_mean_value : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (T N y : ℝ) (a : ℕ → ℂ), 1 ≤ T →
    (2 * q * T) ^ 2 ≤ N → ∑ χ : DirichletCharacter ℂ q, (∫ t in (-T)..T,
      ‖∑ p ∈ primesIoc N y, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * ∑ p ∈ primesIoc N y, (p : ℝ) * ‖a p‖ ^ 2 / Real.log p := by
  obtain ⟨C, hC, hG⟩ := GlobalTheory.GallagherLemma.gallagher
  obtain ⟨B, hB0, hB⟩ := _root_.GlobalTheory.Lin.brun_titchmarsh_const
  refine ⟨C * (4 * B), by positivity, fun q _ T N y a hT hN => ?_⟩
  have hδ : 0 ≤ 1 / T := by positivity
  have hN0 : 0 ≤ N := (sq_nonneg _).trans hN
  set P := primesIoc N y with hP
  have hmem : ∀ p ∈ P, N < p ∧ (p : ℝ) ≤ y ∧ p.Prime := fun p hp => (mem_primesIoc hN0).1 hp
  have hsub : P ⊆ Finset.Icc 1 ⌊y⌋₊ := fun p hp =>
    Finset.mem_Icc.2 ⟨(hmem p hp).2.2.one_le, Nat.le_floor (hmem p hp).2.1⟩
  have hgal : ∀ χ : DirichletCharacter ℂ q, (∫ t in (-T)..T,
      ‖∑ p ∈ P, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * T ^ 2 * ∫ x in Set.Ioi (0 : ℝ), ‖∑ n ∈ P.filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod q)‖ ^ 2 / x := by
    intro χ
    have h := hG ⌊y⌋₊ (fun n => if n ∈ P then a n * χ (n : ZMod q) else 0) T hT
    have r1 : ∀ t : ℝ, ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (if n ∈ P then a n * χ (n : ZMod q) else 0) *
        (n : ℂ) ^ (-(t * I)) = ∑ p ∈ P, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I)) := by
      intro t
      simp_rw [ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
    have r2 : ∀ x : ℝ, ∑ n ∈ (Finset.Icc 1 ⌊y⌋₊).filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)),
        (if n ∈ P then a n * χ (n : ZMod q) else 0) = ∑ n ∈ P.filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod q) := by
      intro x
      rw [Finset.sum_ite_mem, Finset.filter_inter, Finset.inter_eq_right.2 hsub]
    simp_rw [r1, r2] at h
    exact h
  refine (Finset.sum_le_sum fun χ _ => hgal χ).trans ?_
  rw [← Finset.mul_sum]
  set w : ℕ → ℝ := fun n => 4 * B * n / (T * Real.log n) * ‖a n‖ ^ 2 with hw
  have hk : ∀ n ∈ P, (0 : ℝ) < n := fun n hn => by exact_mod_cast (hmem n hn).2.2.pos
  have hint : ∀ n ∈ P, Integrable (fun x : ℝ => w n *
      (if x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T) then 1 / x else 0))
      (volume.restrict (Set.Ioi 0)) := fun n hn =>
    (GlobalTheory.HybridLargeSieve.kernel_integral n (1 / T) (hk n hn) hδ).1.const_mul _
  have key := GlobalTheory.HybridLargeSieve.sum_integral_le (Finset.univ : Finset (DirichletCharacter ℂ q))
    (volume.restrict (Set.Ioi 0))
    (fun χ x => ‖∑ n ∈ P.filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n * χ (n : ZMod q)‖ ^ 2 / x)
    (fun x => ∑ n ∈ P, w n *
      (if x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T) then 1 / x else 0))
    (fun p => by
      refine Measurable.aestronglyMeasurable ?_
      simp_rw [Finset.sum_filter]
      refine Measurable.div (Measurable.pow_const (Measurable.norm ?_) 2) measurable_id
      refine Finset.measurable_sum _ fun n _ => Measurable.ite ?_ measurable_const measurable_const
      exact (measurableSet_lt measurable_id measurable_const).inter
        (measurableSet_le measurable_const (measurable_id.mul_const _)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx p
      have hx' : 0 < x := hx
      positivity)
    (integrable_finsetSum _ hint)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : 0 < x := hx
      have hwin := window B hB0 hB q T N x a (P.filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T))) hT hN hx' (fun n hn => by
          obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hn
          exact ⟨(hmem n h1).2.2, (hmem n h1).1, h2.1, h2.2⟩)
      rw [← Finset.sum_div]
      refine (div_le_div_of_nonneg_right hwin hx'.le).trans (le_of_eq ?_)
      rw [Finset.sum_filter, Finset.sum_div]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs
      · rw [mul_one_div]
      · simp)
  refine (mul_le_mul_of_nonneg_left key (by positivity)).trans ?_
  rw [integral_finsetSum _ hint, mul_assoc, mul_assoc, Finset.mul_sum, Finset.mul_sum _ _ (4 * B)]
  refine mul_le_mul_of_nonneg_left (le_of_eq (Finset.sum_congr rfl fun n hn => ?_)) hC.le
  rw [integral_const_mul, (GlobalTheory.HybridLargeSieve.kernel_integral n (1 / T) (hk n hn) hδ).2]
  simp only [hw]
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (hmem n hn).2.2.one_lt)
  field_simp

end GlobalTheory.PrimeMeanValue
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimeMeanValueCharactersTwistIntegralLe =====
