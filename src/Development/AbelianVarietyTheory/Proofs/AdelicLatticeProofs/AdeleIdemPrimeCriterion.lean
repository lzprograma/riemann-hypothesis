module

public import Formalism.UnipotentAdelicQuotients.ThmBInHecke
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in
private lemma one_lt_valued_inv_iff_mem {E : Type} [Field E] [NumberField E]
    (Q : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) (hx : x ≠ 0) :
    1 < Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q) ↔ x ∈ Q.asIdeal := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
    ← HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact one_lt_inv₀ (zero_lt_iff.mpr (Q.intValuation_ne_zero x hx))


open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in
theorem _root_.GlobalTheory.adele_idem_prime_criterion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Φ : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E)), (∀ x : E, Φ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E y ∈ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ (e : _root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (ε : _root_.HeckeCharacterZeroLocus.ThmBIn.AF F), _root_.HeckeCharacterZeroLocus.ThmBIn.IsPlaceIdem F v ε → e * e = e → e * algebraMap (_root_.HeckeCharacterZeroLocus.ThmBIn.AF F) (_root_.HeckeCharacterZeroLocus.ThmBIn.AE F E) ε = e → ((∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ _root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E (e * _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E ((x : E)⁻¹)) ∉ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E)) ↔ ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0)) := by
  intro F E _ _ _ _ _ Φ hΦ hint hplace e P v ε hε he heε
  obtain ⟨h0, -⟩ := hplace v ε hε
  have ha : (Φ e).1 = 0 := by
    have h := congrArg (fun z => (Φ z).1) heε
    simp only [map_mul, Prod.fst_mul, h0, mul_zero] at h
    exact h.symm
  have hidem : ∀ Q, (Φ e).2 Q = 0 ∨ (Φ e).2 Q = 1 := by
    intro Q
    have h := congrArg (fun z => (Φ z).2 Q) he
    rw [map_mul] at h
    exact IsIdempotentElem.iff_eq_zero_or_one.mp h
  have key : ∀ x : 𝓞 E, x ≠ 0 → (_root_.HeckeCharacterZeroLocus.ThmBIn.finPart F E (e * _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E ((x : E)⁻¹)) ∉ _root_.HeckeCharacterZeroLocus.ThmBIn.intAE F E ↔
      ∃ Q, (Φ e).2 Q = 1 ∧ x ∈ Q.asIdeal) := by
    intro x hx
    rw [hint, map_mul, hΦ]
    push Not
    constructor
    · rintro ⟨Q, hQ⟩
      change 1 < Valued.v ((Φ e).2 Q * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q) at hQ
      rcases hidem Q with h | h
      · rw [h, zero_mul, map_zero] at hQ
        exact absurd hQ (not_lt.mpr zero_le')
      · rw [h, one_mul, one_lt_valued_inv_iff_mem Q x hx] at hQ
        exact ⟨Q, h, hQ⟩
    · rintro ⟨Q, h, hQ⟩
      refine ⟨Q, ?_⟩
      change 1 < Valued.v ((Φ e).2 Q * (algebraMap E (FiniteAdeleRing (𝓞 E) E) (x : E)⁻¹) Q)
      rw [h, one_mul, one_lt_valued_inv_iff_mem Q x hx]
      exact hQ
  constructor
  · intro hcrit
    have hS : ∀ Q, (Φ e).2 Q = 1 → Q = P := by
      intro Q hQ
      by_contra hne
      have hnle : ¬ Q.asIdeal ≤ P.asIdeal := fun hle =>
        hne (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top hle))
      obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.mp hnle
      have hx : x ≠ 0 := fun h => hxP (h ▸ P.asIdeal.zero_mem)
      exact hxP ((hcrit x hx).mpr ((key x hx).mpr ⟨Q, hQ, hxQ⟩))
    obtain ⟨x, hxP, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    obtain ⟨Q, hQ, -⟩ := (key x hx).mp ((hcrit x hx).mp hxP)
    have hQP := hS Q hQ
    subst hQP
    refine ⟨ha, hQ, fun R hR => ?_⟩
    rcases hidem R with h | h
    · exact h
    · exact absurd (hS R h) hR
  · rintro ⟨-, hP, hQ⟩ x hx
    rw [key x hx]
    constructor
    · exact fun hxP => ⟨P, hP, hxP⟩
    · rintro ⟨Q, h, hxQ⟩
      by_cases hQP : Q = P
      · exact hQP ▸ hxQ
      · rw [hQ Q hQP] at h
        exact absurd h zero_ne_one

end GlobalTheory
