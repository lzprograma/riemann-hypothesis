module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocalRep
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocalRep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] in
theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) :=
  GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_mul hf hg


omit [Fintype K] in
theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a :=
  GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_add hf hg


omit [Fintype K] in
theorem isMultiHomog_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 :=
  GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_C r


omit [Fintype K] in
theorem isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) :=
  GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_X ⟨k, i⟩

theorem isMultiHomog_chartMono (c : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k) e :=
  GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_chartMono c e

theorem exists_form_of_mem_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {x : Ω} (hx : x ∈ chartRingZ y c) :
    ∃ (N : K → ℕ) (H : MRing ι), IsMultiHomog H N ∧ aeval y H = x * ∏ k, y ⟨k, c k⟩ ^ N k := by
  classical
  induction hx using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hu
    refine ⟨Pi.single k 1, X ⟨k, i⟩, isMultiHomog_X k i, ?_⟩
    rw [aeval_X, Finset.prod_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    simp only [Pi.single_eq_same, pow_one]
    exact (div_mul_cancel₀ _ (hc k)).symm
  | algebraMap r =>
    exact ⟨0, C r, isMultiHomog_C r, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨N₁, H₁, h₁, e₁⟩ := hu
    obtain ⟨N₂, H₂, h₂, e₂⟩ := hv
    refine ⟨N₁ + N₂, H₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₂ k + H₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₁ k,
      isMultiHomog_add (isMultiHomog_mul h₁ (isMultiHomog_chartMono c N₂))
        (add_comm N₂ N₁ ▸ isMultiHomog_mul h₂ (isMultiHomog_chartMono c N₁)), ?_⟩
    simp only [map_add (f := _), map_mul, map_prod, map_pow, aeval_X, e₁, e₂, Pi.add_apply, pow_add,
      Finset.prod_mul_distrib]
    ring
  | mul u v _ _ hu hv =>
    obtain ⟨N₁, H₁, h₁, e₁⟩ := hu
    obtain ⟨N₂, H₂, h₂, e₂⟩ := hv
    refine ⟨N₁ + N₂, H₁ * H₂, isMultiHomog_mul h₁ h₂, ?_⟩
    simp only [map_mul, e₁, e₂, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring

theorem proof : LocalRep.Statement := by
  intro K _ ι _ Ω _ y a n s z hs hz
  classical
  choose c hzc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hzc k
    have hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y (X ⟨k, c k⟩) = 0
      simp [mConeMap, h0]
    simpa using hz.2 _ hmem
  obtain ⟨N, H, hH, he⟩ := exists_form_of_mem_chartRingZ y c hyc (hs c hyc)
  refine ⟨N + fun k => ((n : ℤ) * a k).toNat, N + fun k => (-((n : ℤ) * a k)).toNat,
    H * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ ((n : ℤ) * a k).toNat,
    ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (N + fun k => (-((n : ℤ) * a k)).toNat) k,
    isMultiHomog_mul hH (isMultiHomog_chartMono c _), isMultiHomog_chartMono c _, fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_mul, map_prod, map_pow, aeval_X]
    rw [he, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← zpow_add₀ (hyc k)]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_prod, map_pow, map_X, eval_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzc k)

end LocalRep

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
