module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChangeOfModel
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GraphIsometric

section Divisor

variable {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]

theorem mul_mem_sup_span {P : Ideal (MRing κ)} {f g u v : MRing κ} (huv : u * f - v * g ∈ P) :
    ∀ x ∈ P ⊔ Ideal.span {f}, u * x ∈ P ⊔ Ideal.span {g} := by
  intro x hx
  obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  have e : u * (p + c * f) = (u * p + c * (u * f - v * g)) + (c * v) * g := by ring
  rw [e]
  exact Submodule.add_mem_sup (P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ huv))
    (Ideal.mem_span_singleton'.mpr ⟨c * v, rfl⟩)

theorem mem_divSupp_and_multAt_eq {P W : Ideal (MRing κ)} {f g u v : MRing κ} (hf : W ∈ divSupp P f)
    (hu : u ∉ W) (hv : v ∉ W) (huv : u * f - v * g ∈ P) :
    W ∈ divSupp P g ∧ multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  have hvu : v * g - u * f ∈ P := by
    rw [← neg_sub]
    exact P.neg_mem huv
  have hWp : W.IsPrime := hf.1.1.1
  refine ⟨⟨GroundTheory.Heights₂.Heights.NumbersDVR.mem_minimalPrimes_of_mul_mem hu hv (mul_mem_sup_span huv)
    (mul_mem_sup_span hvu) hf.1, hf.2⟩, ?_⟩
  unfold multAt
  rw [dite_eq_left hWp, dite_eq_left hWp,
    GroundTheory.Heights₂.Heights.NumbersDVR.length_localized_eq_of_mul_mem hu hv (mul_mem_sup_span huv)
      (mul_mem_sup_span hvu)]

theorem divCycle_eq_of_local {P : Ideal (MRing κ)} {f g : MRing κ}
    (h : ∀ W : Ideal (MRing κ), W.IsPrime → P ≤ W → IsRelevant W →
      ∃ u v, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P) :
    divCycle P f = divCycle P g := by
  ext W
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  by_cases hf : W ∈ divSupp P f
  · obtain ⟨u, v, hu, hv, huv⟩ := h W hf.1.1.1 (le_sup_left.trans hf.1.1.2) hf.2
    obtain ⟨hg, e⟩ := mem_divSupp_and_multAt_eq hf hu hv huv
    rw [ite_eq_left hf, ite_eq_left hg, e]
  · by_cases hg : W ∈ divSupp P g
    · obtain ⟨u, v, hu, hv, huv⟩ := h W hg.1.1.1 (le_sup_left.trans hg.1.1.2) hg.2
      exact absurd (mem_divSupp_and_multAt_eq hg hv hu (by rw [← neg_sub]; exact P.neg_mem huv)).1 hf
    · rw [ite_eq_right hf, ite_eq_right hg]

end Divisor

section Extend

variable {K K₂ M : Type*} [Zero M]

theorem extend_inl_inl (f : K → M) (k : K) : Function.extend (Sum.inl : K → K ⊕ K₂) f 0 (Sum.inl k) = f k :=
  Sum.inl_injective.extend_apply _ _ _

theorem extend_inl_inr (f : K → M) (k : K₂) : Function.extend (Sum.inl : K → K ⊕ K₂) f 0 (Sum.inr k) = 0 :=
  (Function.extend_apply' _ _ _ (by rintro ⟨_, h⟩; cases h)).trans rfl

theorem extend_inr_inr (f : K₂ → M) (k : K₂) : Function.extend (Sum.inr : K₂ → K ⊕ K₂) f 0 (Sum.inr k) = f k :=
  Sum.inr_injective.extend_apply _ _ _

theorem extend_inr_inl (f : K₂ → M) (k : K) : Function.extend (Sum.inr : K₂ → K ⊕ K₂) f 0 (Sum.inl k) = 0 :=
  (Function.extend_apply' _ _ _ (by rintro ⟨_, h⟩; cases h)).trans rfl

end Extend

section Graph

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem graphMap_X_inlV (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (p : Σ k, ι k) :
    graphMap P g (X (inlV p)) = C (Ideal.Quotient.mk P (X p)) := by
  obtain ⟨k, i⟩ := p
  simp [graphMap, inlV]

theorem graphMap_X_inrV (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (q : Σ k, ι₂ k) :
    graphMap P g (X (inrV q)) = C (Ideal.Quotient.mk P (g q)) * X q.1 := by
  obtain ⟨k, j⟩ := q
  simp [graphMap, inrV]

theorem graphMap_rename_inlV (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (p : MRing ι) :
    graphMap P g (rename inlV p) = C (Ideal.Quotient.mk P p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have e : ((graphMap P g).comp (rename (inlV (ι₂ := ι₂))).toRingHom).comp C =
        ((C : (MRing ι ⧸ P) →+* MvPolynomial K₂ (MRing ι ⧸ P)).comp (Ideal.Quotient.mk P)).comp C :=
      RingHom.ext_int _ _
    exact RingHom.congr_fun e a
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp, graphMap_X_inlV]

theorem rename_mem_graphIdeal {P : Ideal (MRing ι)} (g : (Σ k, ι₂ k) → MRing ι) {p : MRing ι} (hp : p ∈ P) :
    rename inlV p ∈ graphIdeal P g := by
  rw [graphIdeal, RingHom.mem_ker, graphMap_rename_inlV, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

theorem minor_mem (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι) (k : K₂) (j₁ j₂ : ι₂ k) :
    X (inrV ⟨k, j₁⟩) * rename inlV (g ⟨k, j₂⟩) - X (inrV ⟨k, j₂⟩) * rename inlV (g ⟨k, j₁⟩) ∈
      graphIdeal P g := by
  rw [graphIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, graphMap_X_inrV, graphMap_X_inrV,
    graphMap_rename_inlV, graphMap_rename_inlV]
  ring

def numForms (g : (Σ k, ι₂ k) → MRing ι) (j : ∀ k, ι₂ k) (a : K₂ → ℤ) : MRing (Sum.elim ι ι₂) :=
  ∏ k, rename inlV (g ⟨k, j k⟩) ^ (a k).toNat * X (inrV ⟨k, j k⟩) ^ (-a k).toNat

def denForms (g : (Σ k, ι₂ k) → MRing ι) (j : ∀ k, ι₂ k) (a : K₂ → ℤ) : MRing (Sum.elim ι ι₂) :=
  ∏ k, X (inrV ⟨k, j k⟩) ^ (a k).toNat * rename inlV (g ⟨k, j k⟩) ^ (-a k).toNat

theorem wh_form [DecidableEq K] [DecidableEq K₂] {g : (Σ k, ι₂ k) → MRing ι} {δ : K₂ → K → ℕ}
    (hg : ∀ q, IsMultiHomog (g q) (δ q.1)) (q : Σ k, ι₂ k) :
    IsWeightedHomogeneous (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight (Sum.elim ι ι₂))
      (rename inlV (g q)) (Function.extend Sum.inl (δ q.1) 0) :=
  (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).mpr
    (GroundTheory.Heights₂.Heights.Inter.rename_isMultiHomog isBlockMap_inl (hg q))

theorem isMultiHomog_numForms [DecidableEq K] [DecidableEq K₂] {g : (Σ k, ι₂ k) → MRing ι} {δ : K₂ → K → ℕ}
    (hg : ∀ q, IsMultiHomog (g q) (δ q.1)) (j : ∀ k, ι₂ k) (a : K₂ → ℤ) :
    IsMultiHomog (numForms g j a)
      (∑ k, ((a k).toNat • Function.extend Sum.inl (δ k) 0 + (-a k).toNat • Pi.single (Sum.inr k) 1)) := by
  refine (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).mp ?_
  exact IsWeightedHomogeneous.prod _ _ _ fun k _ =>
    ((wh_form hg ⟨k, j k⟩).pow _).mul ((isWeightedHomogeneous_X ℤ _ _).pow _)

theorem isMultiHomog_denForms [DecidableEq K] [DecidableEq K₂] {g : (Σ k, ι₂ k) → MRing ι} {δ : K₂ → K → ℕ}
    (hg : ∀ q, IsMultiHomog (g q) (δ q.1)) (j : ∀ k, ι₂ k) (a : K₂ → ℤ) :
    IsMultiHomog (denForms g j a)
      (∑ k, ((a k).toNat • Pi.single (Sum.inr k) 1 + (-a k).toNat • Function.extend Sum.inl (δ k) 0)) := by
  refine (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).mp ?_
  exact IsWeightedHomogeneous.prod _ _ _ fun k _ =>
    ((isWeightedHomogeneous_X ℤ _ _).pow _).mul ((wh_form hg ⟨k, j k⟩).pow _)

theorem num_den_not_mem {P : Ideal (MRing ι)} (hP : P.IsPrime) (g : (Σ k, ι₂ k) → MRing ι) {j : ∀ k, ι₂ k}
    (hj : ∀ k, g ⟨k, j k⟩ ∉ P) (a : K₂ → ℤ) :
    numForms g j a ∉ graphIdeal P g ∧ denForms g j a ∉ graphIdeal P g := by
  have := Ideal.Quotient.isDomain P
  have h1 : ∀ k, (C (Ideal.Quotient.mk P (g ⟨k, j k⟩)) : MvPolynomial K₂ (MRing ι ⧸ P)) ≠ 0 := by
    intro k
    rw [Ne, MvPolynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hj k
  have h2 : ∀ k, (C (Ideal.Quotient.mk P (g ⟨k, j k⟩)) * X k : MvPolynomial K₂ (MRing ι ⧸ P)) ≠ 0 :=
    fun k => mul_ne_zero (h1 k) (X_ne_zero _)
  constructor
  · rw [numForms, graphIdeal, RingHom.mem_ker]
    simp only [map_prod, map_mul, map_pow, graphMap_rename_inlV, graphMap_X_inrV]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => mul_ne_zero (pow_ne_zero _ (h1 k)) (pow_ne_zero _ (h2 k))
  · rw [denForms, graphIdeal, RingHom.mem_ker]
    simp only [map_prod, map_mul, map_pow, graphMap_rename_inlV, graphMap_X_inrV]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => mul_ne_zero (pow_ne_zero _ (h2 k)) (pow_ne_zero _ (h1 k))

private theorem exists_not_mem_of_basePtFree {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι}
    (hBP : IsBasePtFree P g) {I : Ideal (MRing ι)} (hI : I.IsPrime) (hPI : P ≤ I)
    (hrel : ∀ k', ∃ i, (X ⟨k', i⟩ : MRing ι) ∉ I) (k : K₂) : ∃ j', g ⟨k, j'⟩ ∉ I := by
  by_contra hall
  push Not at hall
  choose i hi using hrel
  obtain ⟨N, hN⟩ := hBP k i
  have hmem := sup_le hPI (Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)) hN
  obtain ⟨k', -, hk'⟩ := Ideal.IsPrime.prod_mem_iff.mp (hI.mem_of_pow_mem N hmem)
  exact hi k' hk'

theorem exists_unit {P : Ideal (MRing ι)} {g : (Σ k, ι₂ k) → MRing ι} (hBP : IsBasePtFree P g)
    (j : ∀ k, ι₂ k) (a : K₂ → ℤ) {W : Ideal (MRing (Sum.elim ι ι₂))} (hW : W.IsPrime)
    (hΓW : graphIdeal P g ≤ W) (hrel : IsRelevant W) :
    ∃ u v, u ∉ W ∧ v ∉ W ∧ u * numForms g j a - v * denForms g j a ∈ graphIdeal P g := by
  have hlin : ∀ k, ∃ j', rename inlV (g ⟨k, j'⟩) ∉ W :=
    exists_not_mem_of_basePtFree hBP (Ideal.comap_isPrime _ W)
      (fun p hp => hΓW (rename_mem_graphIdeal g hp)) fun k' => by
        obtain ⟨i, hi⟩ := hrel (Sum.inl k')
        exact ⟨i, by simpa [inlV] using hi⟩
  choose j' hj' using hlin
  have hy : ∀ k, X (inrV ⟨k, j' k⟩) ∉ W := by
    intro k hyk
    obtain ⟨j'', hj''⟩ := hrel (Sum.inr k)
    have hm := hΓW (minor_mem P g k j'' (j' k))
    have hprod : X (inrV ⟨k, j''⟩) * rename inlV (g ⟨k, j' k⟩) ∈ W := by
      have h := W.add_mem hm (W.mul_mem_right (rename inlV (g ⟨k, j''⟩)) hyk)
      rwa [sub_add_cancel] at h
    exact (hW.mem_or_mem hprod).elim hj'' (hj' k)
  have hnm : ∀ u v : K₂ → MRing (Sum.elim ι ι₂), (∀ k, u k ∉ W) → (∀ k, v k ∉ W) →
      ∏ k, u k * v k ∉ W := fun u v hu hv h => by
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
    exact (hW.mem_or_mem hk).elim (hu k) (hv k)
  refine ⟨∏ k, X (inrV ⟨k, j' k⟩) ^ (a k).toNat * rename inlV (g ⟨k, j' k⟩) ^ (-a k).toNat,
    ∏ k, rename inlV (g ⟨k, j' k⟩) ^ (a k).toNat * X (inrV ⟨k, j' k⟩) ^ (-a k).toNat,
    hnm _ _ (fun k h => hy k (hW.mem_of_pow_mem _ h)) (fun k h => hj' k (hW.mem_of_pow_mem _ h)),
    hnm _ _ (fun k h => hj' k (hW.mem_of_pow_mem _ h)) (fun k h => hy k (hW.mem_of_pow_mem _ h)), ?_⟩
  rw [graphIdeal, RingHom.mem_ker, map_sub, sub_eq_zero]
  simp only [numForms, denForms, map_prod, map_mul, map_pow, graphMap_rename_inlV, graphMap_X_inrV]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  ring

theorem norm_factor {l : ℝ} (hl : l ≠ 0) (t : ℝ) (e : ℤ) :
    t ^ e.toNat * (l * t) ^ (-e).toNat * l ^ e = (l * t) ^ e.toNat * t ^ (-e).toNat := by
  have he : l ^ e = l ^ ((e.toNat : ℤ) - ((-e).toNat : ℤ)) := by rw [Int.toNat_sub_toNat_neg]
  rw [he, zpow_sub₀ hl, zpow_natCast, zpow_natCast, mul_pow, mul_pow]
  field_simp

theorem of_forms {P : Ideal (MRing ι)} (hPp : P.IsPrime) {g : (Σ k, ι₂ k) → MRing ι} {δ : K₂ → K → ℕ}
    {B₁ : HermLine ι} {B : HermLine ι₂} {B₁' B' : HermLine (Sum.elim ι ι₂)}
    (hgh : ∀ q, IsMultiHomog (g q) (δ q.1)) (hBP : IsBasePtFree P g)
    (hj : ∀ k, ∃ j, g ⟨k, j⟩ ∉ P)
    (ha : ∀ k, B₁.a k = ∑ k₂, B.a k₂ * (δ k₂ k : ℤ))
    (hh : ∀ z ∈ mcPts P, B₁.h z = B.h (fun q => eval z (map (Int.castRingHom ℂ) (g q))))
    (hpl : IsPullHerm Sum.inl inlV B₁ B₁') (hpr : IsPullHerm Sum.inr inrV B B') :
    IsIsometricOn (graphIdeal P g) B₁' B' := by
  classical
  choose j hj using hj
  obtain ⟨hf, hg⟩ := num_den_not_mem hPp g hj B.a
  refine ⟨numForms g j B.a, denForms g j B.a, _, _, isMultiHomog_numForms hgh j B.a,
    isMultiHomog_denForms hgh j B.a, hf, hg, ?_,
    divCycle_eq_of_local fun W hW hΓW hrel => exists_unit hBP j B.a hW hΓW hrel, ?_⟩
  · intro x
    rw [hpl.1, hpr.1]
    rcases x with k | k
    · rw [pullDeg, pullDeg, extend_inl_inl, extend_inr_inl, ha k]
      simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, extend_inl_inl, Pi.single_apply,
        reduceCtorEq, ite_false, mul_zero, add_zero, zero_add]
      push_cast
      rw [← Finset.sum_sub_distrib, sub_zero]
      refine Finset.sum_congr rfl fun k₂ _ => ?_
      rw [← sub_mul, Int.toNat_sub_toNat_neg]
    · rw [pullDeg, pullDeg, extend_inl_inr, extend_inr_inr]
      simp [Finset.sum_apply, Pi.single_apply]
      omega
  · intro z hz
    set x : (Σ k, ι k) → ℂ := fun p => z (inlV p) with hxdef
    set y : (Σ k, ι₂ k) → ℂ := fun q => z (inrV q) with hydef
    let gx : (Σ k, ι₂ k) → ℂ := fun q => eval x (map (Int.castRingHom ℂ) (g q))
    have hev : ∀ p : MRing ι,
        eval z (map (Int.castRingHom ℂ) (rename (inlV (ι₂ := ι₂)) p)) = eval x (map (Int.castRingHom ℂ) p) := by
      intro p
      rw [map_rename, eval_rename]
      rfl
    have hx : x ∈ mcPts P := by
      refine ⟨fun k => hz.1 (Sum.inl k), fun p hp => ?_⟩
      rw [← hev]
      exact hz.2 _ (rename_mem_graphIdeal g hp)
    have hlin : ∀ q, eval z (map (Int.castRingHom ℂ) (rename inlV (g q))) = gx q := fun q => hev (g q)
    have hyev : ∀ q, eval z (map (Int.castRingHom ℂ) (X (inrV q) : MRing (Sum.elim ι ι₂))) = y q := by
      intro q
      simp [hydef]
    have hminor : ∀ k (j₁ j₂ : ι₂ k), y ⟨k, j₁⟩ * gx ⟨k, j₂⟩ = y ⟨k, j₂⟩ * gx ⟨k, j₁⟩ := by
      intro k j₁ j₂
      have h := hz.2 _ (minor_mem P g k j₁ j₂)
      simp only [map_sub, map_mul, hlin, hyev] at h
      exact sub_eq_zero.mp h
    let φ : MRing ι →+* ℂ := (eval x).comp (map (Int.castRingHom ℂ))
    have hgx : ∀ k, ∃ j', gx ⟨k, j'⟩ ≠ 0 :=
      exists_not_mem_of_basePtFree hBP (RingHom.ker_isPrime φ)
        (fun p hp => RingHom.mem_ker.mpr (hx.2 p hp)) fun k' => by
          obtain ⟨i, hi⟩ := hx.1 k'
          exact ⟨i, by simp [φ, hi]⟩
    choose jx hjx using hgx
    set c : K₂ → ℂ := fun k => y ⟨k, jx k⟩ / gx ⟨k, jx k⟩ with hcdef
    have hyc : ∀ q : Σ k, ι₂ k, y q = c q.1 * gx q := by
      rintro ⟨k, j₁⟩
      simp only [hcdef]
      rw [div_mul_eq_mul_div, eq_div_iff (hjx k)]
      exact hminor k j₁ (jx k)
    have hc : ∀ k, c k ≠ 0 := by
      intro k hck
      obtain ⟨j₁, hj₁⟩ := hz.1 (Sum.inr k)
      have h := hyc ⟨k, j₁⟩
      rw [hck, zero_mul] at h
      exact hj₁ h
    have hB' : B'.h z = (∏ k, ‖c k‖ ^ B.a k) * B.h gx := by
      rw [hpr.2 z, ← B.smul c _ hc]
      congr 1
      funext q
      exact hyc q
    have hB₁' : B₁'.h z = B.h gx := by
      rw [hpl.2 z]
      exact hh x hx
    rw [hB', hB₁', numForms, denForms]
    simp only [map_prod, map_mul, map_pow, hlin, hyev, hyc, norm_prod, norm_mul, norm_pow]
    rw [← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    exact norm_factor (norm_ne_zero_iff.mpr (hc k)) _ _

end Graph

theorem proof : GraphIsometric.Statement := by
  intro K _ ι ι₂ _ _ P d A B₁ B B₁' B' hP hBP ha hh hpl hpr
  classical
  refine of_forms hP.2.1.1 (δ := fun k => Pi.single k 1) (fun q => ?_) hBP
    (ChangeOfModel.exists_linForm_not_mem hP hBP) (fun k => by
      rw [ha, Finset.sum_eq_single k]
      · simp
      · intro k₂ _ hk₂; simp [Pi.single_eq_of_ne hk₂.symm]
      · simp) (fun z hz => ?_) hpl hpr
  · refine (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).mp ?_
    exact IsWeightedHomogeneous.sum _ _ _ fun i _ =>
      (isWeightedHomogeneous_X ℤ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) ⟨q.1, i⟩).C_mul _
  · convert hh z hz using 2
    funext q
    simp [linForm, linApply]

end GraphIsometric

end GroundTheory.Heights₂.Heights.HilbertSamuel
