module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceConjAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.PlaceHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT

@[expose] public section

open NumberField IsDedekindDomain Matrix Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GalOfCusp UpperTheory.V.Af
open scoped Classical nonZeroDivisors

namespace UpperTheory.V.Z.Int

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {E : Type} [Field E] [NumberField E]

private theorem nu_le_one_iff {w : HeightOneSpectrum (𝓞 E)} {τ : E →+* ℂ} (hτ : τ ∈ Ov ι w)
    (a : E) : nu ι (τ a) ≤ 1 ↔ w.valuation E a ≤ 1 := by
  obtain ⟨u, ψ, h1, h2, h3⟩ := placeHom l ι E τ
  obtain rfl := (h3 w).1 hτ
  have h := h2 (algebraMap E _ a)
  have hv : Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w a
  rwa [h1, hv] at h

private theorem nu_eq_one {w : HeightOneSpectrum (𝓞 E)} {τ : E →+* ℂ} (hτ : τ ∈ Ov ι w)
    {a : E} (ha : w.valuation E a = 1) : nu ι (τ a) = 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have h1 := (nu_le_one_iff ι hτ a).2 ha.le
  have h2 := (nu_le_one_iff ι hτ a⁻¹).2 (by rw [map_inv₀, ha, inv_one])
  have hp : 0 < nu ι (τ a) := norm_pos_iff.2 ((map_ne_zero _).2 ((map_ne_zero τ).2 ha0))
  simp only [nu, map_inv₀, norm_inv] at hp h1 h2 ⊢
  exact le_antisymm h1 ((inv_le_one₀ hp).1 h2)

private theorem exists_place (τ : E →+* ℂ) : ∃ u : HeightOneSpectrum (𝓞 E), τ ∈ Ov ι u := by
  obtain ⟨u, _, _, _, h3⟩ := placeHom l ι E τ
  exact ⟨u, (h3 u).2 rfl⟩

private theorem nu_int (τ : E →+* ℂ) (x : 𝓞 E) : nu ι (τ x) ≤ 1 := by
  obtain ⟨u, hu⟩ := exists_place ι τ
  exact (nu_le_one_iff ι hu _).2 (u.valuation_le_one x)

private theorem exists_gen (w : HeightOneSpectrum (𝓞 E)) :
    ∃ h : ℕ, h ≠ 0 ∧ ∃ α : 𝓞 E, α ≠ 0 ∧ Ideal.span {α} = w.asIdeal ^ h := by
  let I0 : (Ideal (𝓞 E))⁰ := ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩
  obtain ⟨J, hJ⟩ : ∃ J : (Ideal (𝓞 E))⁰, J = I0 ^ Nat.card (ClassGroup (𝓞 E)) := ⟨_, rfl⟩
  have h1 : ClassGroup.mk0 J = 1 := by
    rw [hJ, map_pow, pow_card_eq_one']
  have h2 : (J : Ideal (𝓞 E)).IsPrincipal := (ClassGroup.mk0_eq_one_iff J.2).1 h1
  have h3 : (J : Ideal (𝓞 E)) = w.asIdeal ^ Nat.card (ClassGroup (𝓞 E)) := by
    rw [hJ]
    rfl
  obtain ⟨⟨α, hα⟩⟩ := h2
  have hα' : Ideal.span {α} = w.asIdeal ^ Nat.card (ClassGroup (𝓞 E)) := by
    rw [← h3, hα]
  refine ⟨_, Nat.card_pos.ne', α, ?_, hα'⟩
  rintro rfl
  rw [Ideal.span_singleton_zero] at hα'
  exact pow_ne_zero _ w.ne_bot hα'.symm

private theorem val_gen (w : HeightOneSpectrum (𝓞 E)) {h : ℕ} {α : 𝓞 E} (h0 : α ≠ 0)
    (hs : Ideal.span {α} = w.asIdeal ^ h) :
    w.valuation E (α : E) = (w.valuation E (unif w : E)) ^ h := by
  have h1 : w.valuation E (α : E) = w.intValuation α := w.valuation_of_algebraMap α
  rw [h1, w.intValuation_eq_exp_neg_multiplicity h0, hs, _root_.GlobalTheory.CharVal.val_unif, ← WithZero.exp_nsmul]
  have hm : multiplicity w.asIdeal (w.asIdeal ^ h) = h :=
    multiplicity_pow_self w.ne_bot (by simpa using w.isPrime.ne_top) h
  rw [hm]
  simp

private theorem nu_gen_off {w u : HeightOneSpectrum (𝓞 E)} {h : ℕ} {α : 𝓞 E}
    (hs : Ideal.span {α} = w.asIdeal ^ h) (hne : u ≠ w) {τ : E →+* ℂ} (hτ : τ ∈ Ov ι u) :
    nu ι (τ α) = 1 := by
  have hα : α ∉ u.asIdeal := by
    intro hm
    have hle : w.asIdeal ^ h ≤ u.asIdeal := by
      rw [← hs, Ideal.span_singleton_le_iff_mem]
      exact hm
    have hwu : w.asIdeal ≤ u.asIdeal := u.isPrime.le_of_pow_le hle
    exact hne (HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hwu).symm)
  have hmem := (Finset.mem_filter.1 hτ).2 α
  exact le_antisymm (nu_int ι τ α) (not_lt.1 (fun hlt => hα (hmem.2 hlt)))

private theorem prod_emb (α : 𝓞 E) :
    ∏ τ : E →+* ℂ, τ (α : E) = ((Algebra.norm ℤ α : ℤ) : ℂ) := by
  have h1 := Algebra.norm_eq_prod_embeddings ℚ ℂ (α : E)
  have h2 : ((Algebra.norm ℤ α : ℤ) : ℚ) = Algebra.norm ℚ (α : E) := Algebra.coe_norm_int α
  rw [← h2] at h1
  have h3 : ((Algebra.norm ℤ α : ℤ) : ℂ) = ∏ σ : E →ₐ[ℚ] ℂ, σ (α : E) := by
    rw [← h1]
    simp
  rw [h3]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun τ => rfl)

end SlopeTestRemainingChoices

theorem prodNorm : ProdNorm := by
  intro l _ ι E _ _ w
  have hlt : ∀ τ ∈ Ov ι w, 0 < nu ι (τ (unif w : E)) ∧ nu ι (τ (unif w : E)) < 1 := by
    intro τ hτ
    have hp : 0 < nu ι (τ (unif w : E)) :=
      norm_pos_iff.2 ((map_ne_zero _).2 ((map_ne_zero τ).2 (unif w).ne_zero))
    refine ⟨hp, ?_⟩
    have h1 : ¬ w.valuation E (unif w : E)⁻¹ ≤ 1 := by
      rw [map_inv₀, _root_.GlobalTheory.CharVal.val_unif, not_le, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.2 one_pos
    rw [← nu_le_one_iff ι hτ, not_le] at h1
    simp only [nu, map_inv₀, norm_inv] at hp h1
    exact (one_lt_inv₀ hp).1 h1
  refine ⟨hlt, ?_⟩
  obtain ⟨h, hh, α, h0, hs⟩ := exists_gen w
  have hon : ∀ τ ∈ Ov ι w, nu ι (τ α) = nu ι (τ (unif w : E)) ^ h := by
    intro τ hτ
    have hv : w.valuation E ((α : E) / (unif w : E) ^ h) = 1 := by
      have hu : w.valuation E (unif w : E) ≠ 0 := by
        rw [_root_.GlobalTheory.CharVal.val_unif]
        exact WithZero.exp_ne_zero
      rw [map_div₀, map_pow, val_gen w h0 hs, div_self (pow_ne_zero _ hu)]
    have h1 := nu_eq_one ι hτ hv
    have hp := norm_pos_iff.2 ((map_ne_zero ι.symm).2 ((map_ne_zero τ).2 (unif w).ne_zero))
    rw [map_div₀, map_pow] at h1
    simp only [nu, map_div₀, map_pow, norm_div, norm_pow] at h1 ⊢
    rw [div_eq_mul_inv] at h1
    exact (mul_inv_eq_one₀ (pow_ne_zero _ hp.ne')).1 h1
  have hoff : ∀ τ ∈ (Finset.univ : Finset (E →+* ℂ)), τ ∉ Ov ι w → nu ι (τ α) = 1 := by
    intro τ _ hτ
    obtain ⟨u, hu⟩ := exists_place ι τ
    have hne : u ≠ w := by
      rintro rfl
      exact hτ hu
    exact nu_gen_off ι hs hne hu
  have hall : nu ι ((Algebra.norm ℤ α : ℤ) : ℂ) = (∏ τ ∈ Ov ι w, nu ι (τ (unif w : E))) ^ h := by
    rw [← prod_emb]
    simp only [nu, map_prod, norm_prod] at hoff hon ⊢
    rw [← Finset.prod_subset (Finset.subset_univ (Ov ι w)) hoff, Finset.prod_congr rfl hon,
      Finset.prod_pow]
  have hnorm : (Algebra.norm ℤ α).natAbs = normV w ^ h := by
    rw [← Ideal.absNorm_span_singleton, hs, map_pow]
    rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN : nu ι ((Algebra.norm ℤ α : ℤ) : ℂ) = nu ι (normV w : ℂ) ^ h := by
    simp only [nu, ← norm_pow, ← map_pow]
    rcases Int.natAbs_eq (Algebra.norm ℤ α) with he | he <;> (rw [he, hnorm]; simp)
  have hfin := hall.symm.trans hN
  exact (pow_left_inj₀ (Finset.prod_nonneg fun _ _ => norm_nonneg _) (norm_nonneg _) hh).1 hfin

end UpperTheory.V.Z.Int
