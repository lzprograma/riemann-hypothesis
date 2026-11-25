module

import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionsNonzero
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SmallSectionsNonzero

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in
theorem isMultiHomog_mul {g h : MRing ι} {a b : K → ℕ} (hg : IsMultiHomog g a)
    (hh : IsMultiHomog h b) : IsMultiHomog (g * h) (a + b) :=
  SectionBoundedMul.isMultiHomog_mul hg hh

def chartMono (c : ∀ k, ι k) (d : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ d k

theorem isMultiHomog_chartMono (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (chartMono c d) d :=
  SectionBoundedMul.isMultiHomog_chartMono c d

omit [∀ k, Fintype (ι k)] in
theorem aeval_chartMono (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (chartMono c d) = ∏ k, y ⟨k, c k⟩ ^ d k :=
  SectionBoundedMul.aeval_chartMono y c d

omit [∀ k, Fintype (ι k)] in
theorem eval_chartMono (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k) (d : K → ℕ) :
    eval z (map (Int.castRingHom ℂ) (chartMono c d)) = ∏ k, z ⟨k, c k⟩ ^ d k :=
  SectionBoundedMul.eval_chartMono z c d

theorem mem_mCoordIdeal_of_aeval_eq_zero (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) (h0 : aeval y g = 0) : g ∈ mCoordIdeal y :=
  SectionBoundedMul.mem_mCoordIdeal_of_aeval_eq_zero y hg h0

theorem X_mem_mCoordIdeal (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) (h0 : y p = 0) :
    (X p : MRing ι) ∈ mCoordIdeal y := by
  have hX := GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBoundedMul.isMultiHomog_monomial (ι := ι) (Finsupp.single p 1) 1
  rw [← X] at hX
  exact mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])

theorem exists_form_of_mem_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ chartRingZ y c) :
    ∃ (δ : K → ℕ) (e : MRing ι), IsMultiHomog e δ ∧ aeval y e = x * ∏ k, y ⟨k, c k⟩ ^ δ k :=
  SectionBoundedMul.exists_form_of_mem_chartRingZ y c hc hx

theorem exists_chartForm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) {s : Ω} (hs : s ∈ chartLat y a n)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (N dg : K → ℕ) (g : MRing ι), IsMultiHomog g dg ∧ (∀ k, (dg k : ℤ) = N k + n * a k) ∧
      aeval y g = s * aeval y (chartMono c N) :=
  SectionBoundedMul.exists_chartForm y a n hs c hc

omit [∀ k, Fintype (ι k)] in
theorem one_mem_chartLat (y : (Σ k, ι k) → Ω) (a : K → ℤ) : (1 : Ω) ∈ chartLat y a 0 := by
  intro c _
  simp only [Nat.cast_zero, zero_mul, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]
  exact one_mem _

omit [∀ k, Fintype (ι k)] in
theorem mul_mem_chartLat {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact mul_mem (hs c hc) (ht c hc)

omit [∀ k, Fintype (ι k)] in
theorem pow_mem_chartLat {y : (Σ k, ι k) → Ω} {a : K → ℤ} {w : Ω} (hw : w ∈ chartLat y a 1) :
    ∀ j : ℕ, w ^ j ∈ chartLat y a j
  | 0 => by rw [pow_zero]; exact one_mem_chartLat y a
  | j + 1 => by rw [pow_succ]; exact mul_mem_chartLat (pow_mem_chartLat hw j) hw

theorem isSmallH_one (y : (Σ k, ι k) → Ω) (A : HermLine ι) : IsSmallH (mCoordIdeal y) y A 0 1 := by
  intro dg dh g h z hg hh hdeg he hz
  have hd : dg = dh := funext fun k => by simpa using hdeg k
  subst hd
  have hmem := mem_mCoordIdeal_of_aeval_eq_zero y (GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBoundedMul.isMultiHomog_sub hg hh) (by rw [map_sub, he, one_mul, sub_self])
  have hz0 := hz.2 _ hmem
  simp only [map_sub] at hz0
  rw [sub_eq_zero] at hz0
  rw [hz0, pow_zero, mul_one]

theorem isSmallH_mul {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n m : ℕ} {s t : Ω}
    (hs : s ∈ chartLat y A.a n) (ht : t ∈ chartLat y A.a m)
    (hbs : IsSmallH (mCoordIdeal y) y A n s) (hbt : IsSmallH (mCoordIdeal y) y A m t) :
    IsSmallH (mCoordIdeal y) y A (n + m) (s * t) := by
  have h := SectionBoundedMul.proof _ _ _ y A n m 1 1 s t hs ht
    (isBoundedH_one_of_isSmallH hbs) (isBoundedH_one_of_isSmallH hbt)
  intro dg dh g h' z hg hh hdeg he hz
  simpa using h dg dh g h' z hg hh hdeg he hz

theorem isSmallH_pow {y : (Σ k, ι k) → Ω} {A : HermLine ι} {w : Ω} (hw : w ∈ chartLat y A.a 1)
    (hs : IsSmallH (mCoordIdeal y) y A 1 w) : ∀ j : ℕ, IsSmallH (mCoordIdeal y) y A j (w ^ j)
  | 0 => by rw [pow_zero]; exact isSmallH_one y A
  | j + 1 => by
    rw [pow_succ]
    exact isSmallH_mul (pow_mem_chartLat hw j) hw (isSmallH_pow hw hs j) hs

end SmallSectionsNonzero

open SmallSectionsNonzero in
theorem SmallSectionsNonzero.proof : SmallSectionsNonzero.Statement := by
  intro K _ ι _ Ω _ y D A P0 har _ hA j
  obtain ⟨q, w, hw, hgen, hsm⟩ := hA.gen

  choose c hc using har.2.1.2.2
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (X_mem_mCoordIdeal y ⟨k, c k⟩ h0)

  obtain ⟨u, -, hsum⟩ := hgen c hy
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    simp [hne] at hsum
  exact ⟨w i ^ j, pow_mem_chartLat (hw i) j, pow_ne_zero j hi, isSmallH_pow (hw i) (hsm i) j⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
