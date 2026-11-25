module

import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsBoundedAtOfIsBoundedH
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockMetric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.RegularLocalRing.Defs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionNormSqExtension

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

abbrev val := @PowerBlockMetric.val
abbrev val_spec := @PowerBlockMetric.val_spec
abbrev val_eq := @PowerBlockMetric.val_eq
abbrev rep_add := @PowerBlockMetric.rep_add
abbrev w := @PowerBlockMetric.w
abbrev secNormAt_eq := @PowerBlockMetric.secNormAt_eq

theorem exists_chartData [DecidableEq K] (y : (Σ k, ι k) → Ω) (A : HermLine ι) (m N : ℕ) (v : Fin N → Ω)
    (hv : ∀ j, v j ∈ chartLat y A.a m) (c : ∀ k, ι k) :
    ∃ (d e : K → ℕ) (G : Fin N → MRing ι), (∀ k, (e k : ℤ) = d k + m * A.a k) ∧
      (∀ j, IsMultiHomog (G j) e) ∧ ∀ j, aeval y (G j) = v j * aeval y (GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.chartMon c d) := by
  classical
  by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
  · choose Nn δ G hG hdeg hGv using fun j =>
      GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.exists_chartForm y c hc (fun k => (m : ℤ) * A.a k) (hv j c hc)
    have hN : ∀ j k, Nn j k ≤ ∑ i, Nn i k := fun j k =>
      Finset.single_le_sum (f := fun i => Nn i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    set L : K → ℕ := fun k => ∑ i, Nn i k + ((m : ℤ) * A.a k).natAbs with hL
    refine ⟨L, fun k => ((L k : ℤ) + m * A.a k).toNat, fun j => G j * GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.chartMon c (L - Nn j), fun k => ?_,
      fun j => GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_congr (GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.homog_mul (hG j) (GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.homog_chartMon c _)) fun k => ?_, fun j => ?_⟩
    · simp only [hL]
      generalize ∑ i, Nn i k = S
      generalize (m : ℤ) * A.a k = q
      omega
    · have h1 := hdeg j k
      have h2 := hN j k
      simp only [Pi.add_apply, Pi.sub_apply, hL]
      generalize (m : ℤ) * A.a k = q at *
      generalize ∑ i, Nn i k = S at *
      omega
    · rw [map_mul, hGv j, GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.aeval_chartMon, GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.aeval_chartMon, mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← pow_add, Pi.sub_apply]
      congr 1
      have h2 := hN j k
      simp only [hL]
      omega
  · push Not at hc
    obtain ⟨k0, hk0⟩ := hc
    refine ⟨fun k => 1 + ((m : ℤ) * A.a k).natAbs, fun k => (((1 + ((m : ℤ) * A.a k).natAbs : ℕ) : ℤ) +
      m * A.a k).toNat, fun _ => 0, fun k => ?_, fun _ => GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_zero _, fun j => ?_⟩
    · dsimp only
      generalize (m : ℤ) * A.a k = q
      omega
    · rw [GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.aeval_chartMon, Finset.prod_eq_zero (Finset.mem_univ k0) (by rw [hk0]; simp)]
      simp

def blockDeg (μ : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, μ ⟨k, i⟩


open Classical in
def comp (g : MRing ι) (δ : K → ℕ) : MRing ι :=
  ∑ μ ∈ g.support.filter (fun μ => blockDeg μ = δ), monomial μ (AddMonoidAlgebra.coeff g μ)

theorem homog_comp (g : MRing ι) (δ : K → ℕ) : IsMultiHomog (comp g δ) δ := by
  classical
  intro μ hμ k
  obtain ⟨ν, hν, hμν⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hμ)
  have h1 := MvPolynomial.support_monomial_subset hμν
  rw [Finset.mem_singleton] at h1
  subst h1
  exact congrFun (Finset.mem_filter.mp hν).2 k

theorem sum_comp (g : MRing ι) : ∑ δ ∈ g.support.image blockDeg, comp g δ = g := by
  classical
  unfold comp
  rw [Finset.sum_fiberwise_of_maps_to (fun μ hμ => Finset.mem_image_of_mem _ hμ)]
  exact g.as_sum.symm

theorem comp_eq_zero {g : MRing ι} {δ : K → ℕ} (hδ : δ ∉ g.support.image blockDeg) : comp g δ = 0 := by
  classical
  unfold comp
  refine Finset.sum_eq_zero fun μ hμ => ?_
  exact absurd (Finset.mem_image.mpr ⟨μ, (Finset.mem_filter.mp hμ).1, (Finset.mem_filter.mp hμ).2⟩) hδ

theorem prod_X_pow_eq_monomial' (δ : K → ℕ) :
    (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ δ k) = monomial (Finsupp.equivFunOnFinite.symm δ) 1 := by
  classical
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  symm
  rw [Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_]
  · rfl
  · have h1 : (Finsupp.equivFunOnFinite.symm δ) k = 0 := Finsupp.notMem_support_iff.mp hk
    rw [h1, pow_zero]

theorem comp_mem {y : (Σ k, ι k) → Ω} {g : MRing ι} (hg : g ∈ mCoordIdeal y) (δ : K → ℕ) :
    comp g δ ∈ mCoordIdeal y := by
  classical
  show comp g δ ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [_root_.GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mConeMap_eq_of_isMultiHomog y (homog_comp g δ)]
  suffices aeval y (comp g δ) = 0 by rw [this]; simp
  by_cases hδ : δ ∈ g.support.image blockDeg
  · have h0 : mConeMap y g = 0 := hg

    rw [← sum_comp g, map_sum] at h0
    have h1 : ∀ δ' ∈ g.support.image blockDeg, mConeMap y (comp g δ') =
        MvPolynomial.C (aeval y (comp g δ')) * monomial (Finsupp.equivFunOnFinite.symm δ') 1 := fun δ' _ => by
      erw [_root_.GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mConeMap_eq_of_isMultiHomog y (homog_comp g δ'), prod_X_pow_eq_monomial']
    rw [Finset.sum_congr rfl h1] at h0
    have h2 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.equivFunOnFinite.symm δ)) h0
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at h2
    simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, mul_ite, mul_one, mul_zero,
      EmbeddingLike.apply_eq_iff_eq] at h2
    rw [Finset.sum_ite_eq' _ _ _, ite_eq_left hδ] at h2
    exact h2
  · rw [comp_eq_zero hδ, map_zero]

theorem exists_gens (y : (Σ k, ι k) → Ω) :
    ∃ F : Finset (MRing ι × (K → ℕ)), (∀ p ∈ F, IsMultiHomog p.1 p.2 ∧ p.1 ∈ mCoordIdeal y) ∧
      mCoordIdeal y ≤ Ideal.span ((fun p => p.1) '' (F : Set (MRing ι × (K → ℕ)))) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (mCoordIdeal y) : (mCoordIdeal y).FG)
  refine ⟨s.biUnion fun g => (g.support.image blockDeg).image fun δ => (comp g δ, δ), ?_, ?_⟩
  · intro p hp
    obtain ⟨g, hg, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨homog_comp g δ, comp_mem ?_ δ⟩
    rw [← hs]
    exact Submodule.subset_span hg
  · rw [← hs]
    refine Submodule.span_le.mpr fun g hg => ?_
    rw [← sum_comp g]
    refine Ideal.sum_mem _ fun δ hδ => Ideal.subset_span ⟨(comp g δ, δ), ?_, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image_of_mem _ hδ⟩

theorem mem_mcPts_of_gens {y : (Σ k, ι k) → Ω} {F : Finset (MRing ι × (K → ℕ))}
    (hF : mCoordIdeal y ≤ Ideal.span ((fun p => p.1) '' (F : Set (MRing ι × (K → ℕ)))))
    {x : (Σ k, ι k) → ℂ} (hx : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0)
    (h0 : ∀ p ∈ F, eval x (map (Int.castRingHom ℂ) p.1) = 0) : x ∈ mcPts (mCoordIdeal y) := by
  refine ⟨hx, fun f hf => ?_⟩
  have hle : Ideal.span ((fun p => p.1) '' (F : Set (MRing ι × (K → ℕ)))) ≤
      RingHom.ker ((eval x).comp (map (Int.castRingHom ℂ))) := by
    rw [Ideal.span_le]
    rintro _ ⟨p, hp, rfl⟩
    simpa [RingHom.mem_ker] using h0 p hp
  simpa [RingHom.mem_ker] using hle (hF hf)

theorem norm_eval_rep {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m : ℕ} {s : Ω} (hs : s ∈ chartLat y A.a m)
    {c : ∀ k, ι k} {d e : K → ℕ} {G : MRing ι} (he : ∀ k, (e k : ℤ) = d k + m * A.a k) (hG : IsMultiHomog G e)
    (hGy : aeval y G = s * aeval y (GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.chartMon c d)) {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) :
    ‖eval x (map (Int.castRingHom ℂ) G)‖ =
      secNormAt y A m s x * ‖eval x (map (Int.castRingHom ℂ) (GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.chartMon c d))‖ * A.h x ^ m := by
  rw [secNormAt_eq hs hx, val_spec hs hx ⟨e, d, hG, GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.homog_chartMon c d, he, hGy⟩, norm_mul, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg (A.pos x hx.1).le]

theorem exists_G_ne {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m N : ℕ} {v : Fin N → Ω}
    (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v) {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {d e : K → ℕ} {G : Fin N → MRing ι} (he : ∀ k, (e k : ℤ) = d k + m * A.a k)
    (hG : ∀ j, IsMultiHomog (G j) e) (hGy : ∀ j, aeval y (G j) = v j * aeval y (GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.chartMon c d))
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts (mCoordIdeal y)) (hxc : ∀ k, x ⟨k, c k⟩ ≠ 0) :
    ∃ j, eval x (map (Int.castRingHom ℂ) (G j)) ≠ 0 := by
  obtain ⟨u, hu, hsum⟩ := hgen c hc
  simp only [] at hsum
  choose δ U hU hUy using fun j => GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.exists_form_of_mem_chartRingZ y c hc (hu j)
  have hδ : ∀ j k, δ j k ≤ ∑ i, δ i k := fun j k =>
    Finset.single_le_sum (f := fun i => δ i k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set L : K → ℕ := fun k => ∑ i, δ i k with hL
  set F : MRing ι := ∑ j, U j * GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.chartMon c (L - δ j) * G j - GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.chartMon c (L + e) with hF
  have hFh : IsMultiHomog F (L + e) := by
    refine GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.homog_sub (GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_sum _ fun j _ => GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.homog_congr (GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.homog_mul (GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.homog_mul (hU j) (GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.homog_chartMon c _))
      (hG j)) fun k => ?_) (GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.homog_chartMon c _)
    have := hδ j k
    simp only [Pi.add_apply, Pi.sub_apply, hL] at this ⊢
    omega
  have hpow : ∀ k, y ⟨k, c k⟩ ^ (L k + e k) * y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k)) =
      y ⟨k, c k⟩ ^ (L k + d k) := by
    intro k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k)]
    congr 1
    push_cast
    linarith [he k]
  have e1 : ∀ j, aeval y (U j * GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.chartMon c (L - δ j) * G j) =
      (u j * (v j * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k)))) * ∏ k, y ⟨k, c k⟩ ^ (L k + e k) := by
    intro j
    rw [map_mul, map_mul, hUy j, hGy j, GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.aeval_chartMon, GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.aeval_chartMon]
    have h3 : ∀ k, y ⟨k, c k⟩ ^ δ j k * y ⟨k, c k⟩ ^ (L - δ j) k * y ⟨k, c k⟩ ^ d k =
        y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k)) * y ⟨k, c k⟩ ^ (L k + e k) := by
      intro k
      rw [mul_comm (y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))), hpow k, ← pow_add, ← pow_add]
      congr 1
      have := hδ j k
      simp only [Pi.sub_apply, hL] at this ⊢
      omega
    calc _ = u j * v j * ∏ k, (y ⟨k, c k⟩ ^ δ j k * y ⟨k, c k⟩ ^ (L - δ j) k * y ⟨k, c k⟩ ^ d k) := by
          simp only [Finset.prod_mul_distrib]
          ring
      _ = _ := by
          rw [Finset.prod_congr rfl fun k _ => h3 k, Finset.prod_mul_distrib]
          ring
  have hFy : aeval y F = 0 := by

    rw [hF, map_sub, map_sum, Finset.sum_congr rfl fun j _ => e1 j, ← Finset.sum_mul, hsum, one_mul,
    GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.aeval_chartMon]
    simp only [Pi.add_apply, sub_self]
  have hFx := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.vanish hx hFh hFy
  by_contra hne
  push Not at hne
  rw [hF] at hFx

  simp only [map_sub, map_sum, map_mul, hne, mul_zero, Finset.sum_const_zero, zero_sub, neg_eq_zero,
  GroundTheory.Heights₂.Heights.HilbertSamuel.PowerBlockMetric.eval_chartMon] at hFx
  exact (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hxc k)) hFx

end SectionNormSqExtension

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
