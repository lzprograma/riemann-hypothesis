module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Bridge

open MvPolynomial

noncomputable section

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem isRelevant_iff (W : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsRelevant W ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (R := R) W := Iff.rfl

section Homog

variable [DecidableEq K] [∀ k, Fintype (ι k)]

theorem weight_blockWeight (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight ι) m = fun k => ∑ i, m ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  simp only [NumbersDVR.blockWeight, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  classical
  set T : Finset (Σ k, ι k) := (Finset.univ : Finset (ι k)).map ⟨Sigma.mk k, sigma_mk_injective⟩
  have h1 : ∑ x ∈ m.support, (if k = x.1 then m x else 0) =
      ∑ x ∈ m.support ∪ T, (if k = x.1 then m x else 0) := by
    refine Finset.sum_subset Finset.subset_union_left fun x _ hx => ?_
    rw [Finsupp.notMem_support_iff.mp hx, ite_self]
  have h2 : ∑ x ∈ T, (if k = x.1 then m x else 0) =
      ∑ x ∈ m.support ∪ T, (if k = x.1 then m x else 0) := by
    refine Finset.sum_subset Finset.subset_union_right fun x _ hx => ?_
    rw [ite_eq_right]
    rintro rfl
    exact hx (Finset.mem_map.mpr ⟨x.2, Finset.mem_univ _, rfl⟩)
  rw [h1, ← h2, Finset.sum_map]
  simp

theorem isMultiHomog_iff (f : NumbersDVR.MRing ι R) (a : K → ℕ) :
    NumbersDVR.IsMultiHomog f a ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) f a := by
  unfold NumbersDVR.IsMultiHomog ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog IsWeightedHomogeneous
  simp only [weight_blockWeight, mem_support_iff, funext_iff]

theorem isMultiHomog_X (p : Σ k, ι k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (X p) (Pi.single p.1 1) :=
  (isMultiHomog_iff _ _).mp (isWeightedHomogeneous_X R (NumbersDVR.blockWeight ι) p)

theorem isMultiHomog_X_ite (p : Σ k, ι k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (X p) (fun k => if k = p.1 then 1 else 0) := by
  convert isMultiHomog_X (R := R) p; simp [Pi.single_apply]

end Homog

section HomogOps

variable [∀ k, Fintype (ι k)]

theorem isMultiHomog_zero (a : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (0 : NumbersDVR.MRing ι R) a := by
  classical exact (isMultiHomog_iff _ _).mp (isWeightedHomogeneous_zero R _ a)

theorem isMultiHomog_C (r : R) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (C r : NumbersDVR.MRing ι R) 0 := by
  classical exact (isMultiHomog_iff _ _).mp (isWeightedHomogeneous_C _ r)

theorem isMultiHomog_one :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (1 : NumbersDVR.MRing ι R) 0 := by
  classical exact (isMultiHomog_iff _ _).mp (isWeightedHomogeneous_one R _)

theorem isMultiHomog_monomial (d : (Σ k, ι k) →₀ ℕ) (r : R) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (monomial d r) (fun k => ∑ i, d ⟨k, i⟩) := by
  classical exact (isMultiHomog_iff _ _).mp (weight_blockWeight d ▸ isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) d r rfl)

theorem isMultiHomog_add {f g : NumbersDVR.MRing ι R} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (f + g) a := by
  classical exact (isMultiHomog_iff _ _).mp (((isMultiHomog_iff _ _).mpr hf).add ((isMultiHomog_iff _ _).mpr hg))

theorem isMultiHomog_neg {f : NumbersDVR.MRing ι R} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (-f) a := by
  classical exact (isMultiHomog_iff _ _).mp (((isMultiHomog_iff _ _).mpr hf).neg)

theorem isMultiHomog_sub {f g : NumbersDVR.MRing ι R} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (f - g) a := by
  classical exact (isMultiHomog_iff _ _).mp (((isMultiHomog_iff _ _).mpr hf).sub ((isMultiHomog_iff _ _).mpr hg))

theorem isMultiHomog_mul {f g : NumbersDVR.MRing ι R} {a b : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) f a)
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) g b) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (f * g) (a + b) := by
  classical exact (isMultiHomog_iff _ _).mp (((isMultiHomog_iff _ _).mpr hf).mul ((isMultiHomog_iff _ _).mpr hg))

theorem isMultiHomog_pow {f : NumbersDVR.MRing ι R} {a : K → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) f a) (n : ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (f ^ n) (n • a) := by
  classical exact (isMultiHomog_iff _ _).mp (((isMultiHomog_iff _ _).mpr hf).pow n)

theorem isMultiHomog_sum {β : Type*} (s : Finset β) (f : β → NumbersDVR.MRing ι R) {a : K → ℕ}
    (h : ∀ b ∈ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (f b) a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (∑ b ∈ s, f b) a := by
  classical exact (isMultiHomog_iff _ _).mp (IsWeightedHomogeneous.sum s f a fun b hb => (isMultiHomog_iff _ _).mpr (h b hb))

theorem isMultiHomog_prod {β : Type*} (s : Finset β) (f : β → NumbersDVR.MRing ι R) (a : β → K → ℕ)
    (h : ∀ b ∈ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (f b) (a b)) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical exact (isMultiHomog_iff _ _).mp (IsWeightedHomogeneous.prod s f a fun b hb => (isMultiHomog_iff _ _).mpr (h b hb))

theorem isMultiHomog_chartMono [Fintype K] (c : ∀ k, ι k) (d : K → ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R)
      (∏ k, (X ⟨k, c k⟩ : NumbersDVR.MRing ι R) ^ d k) d := by
  classical
  convert isMultiHomog_prod (R := R) Finset.univ (fun k => (X ⟨k, c k⟩ : NumbersDVR.MRing ι R) ^ d k)
    (fun k => d k • Pi.single k 1) fun k _ => isMultiHomog_pow (isMultiHomog_X (R := R) ⟨k, c k⟩) (d k)
  ext k; simp [Finset.sum_apply, Pi.single_apply]

end HomogOps

section Ideals

variable [DecidableEq K] [∀ k, Fintype (ι k)]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_iff (P : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsMultiHomogIdeal P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := R) P := by
  classical
  constructor
  · intro h
    refine ⟨{g | ∃ f ∈ P, ∃ b, g = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f},
      ?_, le_antisymm ?_ ?_⟩
    · rintro g ⟨f, -, b, rfl⟩
      exact ⟨b, (isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous b f)⟩
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, b, rfl⟩
      exact h f hf b
  · rintro ⟨S, hS, rfl⟩ f hf b
    have hom : (Ideal.span S).IsHomogeneous
        (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) := by
      refine Ideal.homogeneous_span _ S fun x hx => ?_
      obtain ⟨a, ha⟩ := hS x hx
      exact ⟨a, (isMultiHomog_iff x a).mpr ha⟩
    exact weightedHomogeneousComponent_mem_of_mem (h := hom) (hp := hf) (m := b)

theorem isMultiProjPrime_iff (P : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsMultiProjPrime P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (R := R) P :=
  ⟨fun h => ⟨h.isPrime, (isMultiHomogIdeal_iff P).mp h.multiHomog, h.relevant⟩,
    fun h => ⟨h.1, (isMultiHomogIdeal_iff P).mpr h.2.1, h.2.2⟩⟩

end Ideals

section Cycles

theorem multAt_eq_toNat (J W : Ideal (NumbersDVR.MRing ι R)) [W.IsPrime] :
    ReciprocityTheory.ChartRestriction.G.Geo.multAt (R := R) J W = (NumbersDVR.multAt J W).toNat := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.multAt NumbersDVR.multAt
  rw [dite_eq_left ‹W.IsPrime›]

theorem divCycle_eq [Fintype K] [∀ k, Fintype (ι k)] [IsNoetherianRing R]
    (P : Ideal (NumbersDVR.MRing ι R)) (f : NumbersDVR.MRing ι R) (W : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.divCycle P f W = (ReciprocityTheory.ChartRestriction.G.Geo.divCycle (R := R) P f W : ℤ) := by
  classical
  unfold NumbersDVR.divCycle ReciprocityTheory.ChartRestriction.G.Geo.divCycle
  simp only [Finsupp.ofSupportFinite_coe, ReciprocityTheory.ChartRestriction.G.Geo.divSupp, Set.mem_ofPred_eq,
    ← isRelevant_iff]
  split_ifs with h
  · have : W.IsPrime := h.1.1.1
    rw [multAt_eq_toNat]
  · rfl

end Cycles

end

end GroundTheory.Heights₂.Heights.Bridge
