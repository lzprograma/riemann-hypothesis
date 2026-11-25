module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLieDataCircle
public import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsIntMulIsIntegralOfTrace
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsShortOfTraceDet
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.SmoothForms GlobalTheory.HermClass Module Submodule NumberField Matrix

namespace GlobalTheory.SmoothForms.Short

theorem one_le_norm_mul_pow {E : Type} [Field E] [NumberField E] {a : E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0)
    {T : ℝ} (hT : 1 ≤ T) (haT : house a ≤ T) (ψ : E →+* ℂ) : 1 ≤ ‖ψ a‖ * T ^ finrank ℚ E := by
  classical
  have h1 : (1 : ℝ) ≤ ∏ φ : E →+* ℂ, ‖φ a‖ := by
    have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
    rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ a) _ (fun _ => rfl)] at h
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm ℚ ha)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (Algebra.norm_ne_zero_iff (R := ℚ)).2 h0 (by rw [← hm, map_zero])
    rw [← norm_prod, ← h, ← hm]
    simp only [algebraMap_int_eq, eq_intCast, eq_ratCast, Rat.cast_intCast, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hm0
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ψ)] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  refine (Finset.prod_le_prod₀ (g := fun _ => T) (fun _ _ => norm_nonneg _)
    fun φ _ => (norm_le_pi_norm (canonicalEmbedding E a) φ).trans haT).trans ?_
  rw [Finset.prod_const, ← Embeddings.card E ℂ]
  exact pow_le_pow_right₀ hT (Finset.card_le_univ _)

theorem exists_imaginary (E : Type) [Field E] [NumberField E] [IsCMField E] :
    ∃ δ : E, δ ≠ 0 ∧ IsIntegral ℤ δ ∧ star δ = -δ := by
  obtain ⟨x, hx⟩ : ∃ x : E, star x ≠ x := by
    by_contra hc
    push Not at hc
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext hc)
  obtain ⟨M, hM, hMa⟩ := exists_int_mul_isIntegral E (Set.finite_singleton x)
  have hi := hMa x rfl
  refine ⟨M * x - star (M * x), ?_, hi.sub (isIntegral_star hi), by simp⟩
  rw [star_mul', star_intCast, ← mul_sub]
  exact mul_ne_zero (by exact_mod_cast hM) (sub_ne_zero.2 hx.symm)

theorem size_sum_le {E : Type} [Field E] [NumberField E] [IsCMField E]
    {V : Type} [AddCommGroup V] [Module E V] {h : V →ₗ[E] V →ₗ⋆[E] E} {Λ : Submodule ℤ V} {N : ℤ}
    {ν : V → ℝ} {B : ℝ} (H : Sized h Λ N ν B) {ι : Type} (s : Finset ι) (f : ι → V) :
    ν (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ν (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := H.smul_le 0 0
    simpa [house] using this
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (H.add_le _ _).trans (by linarith)

theorem shortSmall (E : Type) [Field E] [NumberField E] [IsCMField E] (hfr : FrameSmall E) : ShortSmall E := by
  classical
  intro n hn N hN
  obtain ⟨k, hk⟩ := hfr n
  obtain ⟨D, hD, hDa⟩ := exists_int_mul_isIntegral_of_trace E
  obtain ⟨δ, hδ0, hδi, hδ⟩ := exists_imaginary E
  set F := maximalRealSubfield E with hF
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt
    ((2 * n : ℕ) * (|((N * D * 2 : ℤ) : ℝ)| + 1) + (1 + house δ)) (one_lt_two (α := ℝ))
  refine ⟨(2 * n : ℕ) * (|((N * D * 2 : ℤ) : ℝ)| + 1) ^ 2,
    m + (1 + (m + k) * 2) * finrank ℚ E + (m + k), ?_⟩
  intro V _ _ _ h Λ ν B hV H
  have hsp : span E (Λ : Set V) = ⊤ := by
    rw [eq_top_iff, ← H.span]; exact span_mono fun x hx => hx.1
  obtain ⟨e, heΛ, heo, he⟩ := hk V h Λ N ν B hV H
  obtain ⟨κ, _, _, b, q, hbΛ, hbZ, hq, _, hκ, hT0, hT1⟩ :=
    exists_trace_det_basis hn hN hD hDa h Λ hV H.symm H.fg hsp H.stable H.dual
  have : FiniteDimensional F V := Module.Finite.trans E V
  have hFV : finrank F V = 2 * n := by
    rw [← finrank_mul_finrank F E V, hV, Algebra.IsQuadraticExtension.finrank_eq_two]
  set M : ℝ := |((N * D * 2 : ℤ) : ℝ)| with hM
  let s : Bool → E := fun u => if u then δ else 1
  have hs0 : ∀ u, s u ≠ 0 := fun u => by cases u <;> simp [s, hδ0]
  have hsi : ∀ u, IsIntegral ℤ (s u) := fun u => by cases u <;> simp [s, hδi, isIntegral_one]
  have hsh : ∀ u, house (s u) ≤ 1 + house δ := fun u => by
    have h1 := house_intCast (K := E) 1
    have h2 := house_nonneg δ
    cases u <;> simp [s] at h1 ⊢
    linarith
  let g : Fin n × Bool → V := fun p => s p.2 • e p.1
  have hgΛ : ∀ p, g p ∈ Λ := fun p => H.stable _ (hsi _) _ (heΛ _)
  have hgo : ∀ p l, l ≠ p → q (g l) (g p) = 0 := by
    rintro ⟨i, u⟩ ⟨j, w⟩ hne
    apply Subtype.ext
    rw [hq]
    by_cases hij : j = i
    · subst hij
      have : w ≠ u := fun h0 => hne (by rw [h0])
      cases u <;> cases w <;> simp [g, s, starRingEnd_apply, hδ] at this ⊢
    · simp [g, heo j i hij, heo i j (Ne.symm hij)]
  have hg0 : ∀ p, (q (g p) (g p) : E) ≠ 0 := fun p => by
    rw [hq, ← two_mul]
    simp [g, hs0, (he p.1).1]
  have hgli : LinearIndependent F g := LinearMap.linearIndependent_of_isOrthoᵢ (B := q)
    (fun p l hpl => hgo l p hpl) fun p h0 => hg0 p (by rw [h0]; rfl)
  have hcι : Fintype.card (Fin n × Bool) = 2 * n := by simp [mul_comm]
  let γ : Basis (Fin n × Bool) F V := basisOfLinearIndependentOfCardEqFinrank' g hgli (by rw [hcι, hFV])
  have hγ : ∀ p, γ p = g p := fun p => by simp [γ]
  obtain ⟨z, hz0, hz⟩ := exists_short_coord γ q (fun p l hl => by rw [hγ, hγ]; exact hgo p l hl) b
    (by rw [hκ, hcι]) (t := M + 1) (by positivity) hT0 hT1
  refine ⟨∑ i, z i • b i, sum_mem fun i _ => Λ.smul_mem _ (hbΛ i), fun h0 => hz0 ?_, ?_, ?_⟩
  · exact funext (Fintype.linearIndependent_iff.1 hbZ z h0)
  · rw [house, pi_norm_le_iff_of_nonneg (by positivity)]
    intro φ
    have h1 := (hz (φ.comp (algebraMap F E))).1
    rw [hcι] at h1
    refine le_trans ?_ h1
    change ‖φ (h _ _)‖ ≤ ‖φ (q _ _ : E)‖
    rw [hq, ← two_mul, map_mul, norm_mul, map_ofNat, Complex.norm_ofNat]
    linarith [norm_nonneg (φ (h (∑ i, z i • b i) (∑ i, z i • b i)))]
  · set v := ∑ i, z i • b i with hv
    have hB := H.two_le
    have hB1 : 1 ≤ B := by linarith
    have hBm : (2 : ℝ) ^ m ≤ B ^ m := pow_le_pow_left₀ (by norm_num) hB m
    have hδn := house_nonneg δ
    have hn0 : (0 : ℝ) ≤ (2 * n : ℕ) * (M + 1) := by positivity
    have hgν : ∀ p, ν (g p) ≤ B ^ (m + k) := fun p => by
      refine (H.smul_le _ _).trans ?_
      rw [pow_add]
      exact mul_le_mul ((hsh _).trans (by linarith)) (he p.1).2 (H.nonneg _) (by positivity)
    have hga : ∀ p, house (q (g p) (g p) : E) ≤ B ^ (1 + (m + k) * 2) := fun p => by
      rw [hq, pow_add, pow_one, pow_mul]
      refine (house_add_le _ _).trans ?_
      have h1 : house (h (g p) (g p)) ≤ (B ^ (m + k)) ^ 2 := by
        refine (H.form_le _ _).trans ?_
        rw [sq]
        exact mul_le_mul (hgν p) (hgν p) (H.nonneg _) (by positivity)
      have h2 : 0 ≤ (B ^ (m + k)) ^ 2 := by positivity
      nlinarith
    set U : ℝ := (B ^ (1 + (m + k) * 2)) ^ finrank ℚ E with hU
    have hU1 : 1 ≤ U := one_le_pow₀ (one_le_pow₀ hB1)
    have hc : ∀ p, house (γ.repr v p : E) ≤ (M + 1) * U := fun p => by
      rw [house, pi_norm_le_iff_of_nonneg (by positivity)]
      intro φ
      have h1 : ‖φ (γ.repr v p : E)‖ ^ 2 * ‖φ (q (γ p) (γ p) : E)‖ ≤ (M + 1) ^ 2 :=
        (hz (φ.comp (algebraMap F E))).2 p
      rw [hγ] at h1
      have h2 := one_le_norm_mul_pow (a := (q (g p) (g p) : E))
        (by rw [hq]; exact (H.int _ (hgΛ p) _ (hgΛ p)).add (H.int _ (hgΛ p) _ (hgΛ p))) (hg0 p)
        (one_le_pow₀ hB1) (hga p) φ
      rw [← hU] at h2
      change ‖φ (γ.repr v p : E)‖ ≤ _
      refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
      calc ‖φ (γ.repr v p : E)‖ ^ 2 ≤ ‖φ (γ.repr v p : E)‖ ^ 2 * (‖φ (q (g p) (g p) : E)‖ * U) :=
            le_mul_of_one_le_right (by positivity) h2
        _ ≤ (M + 1) ^ 2 * U := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ ((M + 1) * U) ^ 2 := by
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    calc ν v = ν (∑ p, γ.repr v p • γ p) := by rw [γ.sum_repr]
      _ ≤ ∑ p, ν (γ.repr v p • γ p) := size_sum_le H _ _
      _ ≤ ∑ _p : Fin n × Bool, (M + 1) * U * B ^ (m + k) := Finset.sum_le_sum fun p _ => by
          rw [hγ]
          exact (H.smul_le (γ.repr v p : E) (g p)).trans
            (mul_le_mul (hc p) (hgν p) (H.nonneg _) (by positivity))
      _ = (2 * n : ℕ) * (M + 1) * U * B ^ (m + k) := by
          rw [Finset.sum_const, Finset.card_univ, hcι, nsmul_eq_mul]; ring
      _ ≤ B ^ m * U * B ^ (m + k) := by gcongr; linarith
      _ = _ := by rw [hU, ← pow_mul, ← pow_add, ← pow_add]

end GlobalTheory.SmoothForms.Short
