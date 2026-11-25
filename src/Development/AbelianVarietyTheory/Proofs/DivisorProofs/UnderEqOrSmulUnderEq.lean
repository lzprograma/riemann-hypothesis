module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.UnitaryNorms.CharHost
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.Columns.DecoFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped Pointwise

namespace GlobalTheory.ConjOverQuad

theorem under_eq_or_smul_under_eq {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] {p : ℕ} (hp : p.Prime) (b : L)
    (hb : ∀ σ : L ≃ₐ[ℚ] L, σ b = b ∨ σ b = -b) (c : L ≃ₐ[ℚ] L) (hc : c b = -b)
    (v : Ideal (𝓞 L)) [v.IsPrime] (hv : ((p : ℕ) : 𝓞 L) ∈ v)
    (Q : Ideal (𝓞 (IntermediateField.adjoin ℚ {b}))) [Q.IsPrime]
    (hQ : ((p : ℕ) : 𝓞 (IntermediateField.adjoin ℚ {b})) ∈ Q) :
    v.under (𝓞 (IntermediateField.adjoin ℚ {b})) = Q ∨
      (c⁻¹ • v).under (𝓞 (IntermediateField.adjoin ℚ {b})) = Q := by
  obtain ⟨⟨W, hW, hWQ⟩⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 L)))
  have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
    rw [hWQ.over, Ideal.mem_under] at hQ
    simpa using hQ
  have := GlobalTheory.Mem.Chr.liesOver_span_of_natCast_mem hp _ hv
  have := GlobalTheory.Mem.Chr.liesOver_span_of_natCast_mem hp _ hpW
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) v W (L ≃ₐ[ℚ] L)
  rcases hb σ with h1 | h1
  · left
    rw [hWQ.over, ← hσ, GlobalTheory.Mem.Chr.under_smul_of_fix b σ h1]
  · right
    have h2 : (σ * c) b = b := by
      rw [AlgEquiv.mul_apply, hc, map_neg, h1, neg_neg]
    have h4 : (σ * c) • c⁻¹ • v = W := by rw [mul_smul, smul_inv_smul, hσ]
    rw [hWQ.over, ← h4, GlobalTheory.Mem.Chr.under_smul_of_fix b _ h2]

theorem div_or_conj_div : ∀ (D : D7) (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (w : HeightOneSpectrum (𝓞 D.host.E)), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → P.Div k w ∨ ∃ w' : HeightOneSpectrum (𝓞 D.host.E), P.Div k w' ∧ w'.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) w.asIdeal := by
  intro D P k w hw
  have hG : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hsq := D.host.sqrtMinusD_sq
  have hc := D.host.conj_sqrtMinusD
  have hb : ∀ σ : D.host.E ≃ₐ[ℚ] D.host.E,
      σ D.host.sqrtMinusD = D.host.sqrtMinusD ∨ σ D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    intro σ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, hsq, map_neg, map_natCast]
  have := w.isPrime
  have hQ := (P.pb k).isPrime
  rcases @under_eq_or_smul_under_eq _ _ _ _ _ (D.host.g_prime k) D.host.sqrtMinusD hb D.host.conj hc w.asIdeal _ hw
    (P.pb k).asIdeal hQ (P.pb_over k) with h | h
  · exact Or.inl (HeightOneSpectrum.ext h)
  · refine Or.inr ⟨Formalism.L2.Col.conjPrime₂ w, HeightOneSpectrum.ext ?_, (Formalism.L2.Col.conjIdeal_asIdeal w).symm⟩
    have e : (Formalism.L2.Col.conjPrime₂ w).asIdeal = D.host.conj⁻¹ • w.asIdeal := by
      ext y
      rw [Formalism.L2.Col.mem_conjP, Ideal.mem_inv_pointwise_smul_iff]
      have : Formalism.L2.Col.cO D.host.E y = D.host.conj • y :=
        RingOfIntegers.ext (bridge_star_holds D.R D.host (y : D.host.E))
      rw [this]
    show ((Formalism.L2.Col.conjPrime₂ w).asIdeal).under (𝓞 D.host.K) = _
    rw [e]
    exact h

end GlobalTheory.ConjOverQuad
