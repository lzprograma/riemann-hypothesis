module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularEverywhereIsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Mathlib.RingTheory.LocalRing.LocalSubring

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.ChartVal

theorem isIntegral_of_forall_valuationSubring {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
    (hf : Function.Injective (algebraMap R Ω)) (a : Ω)
    (H : ∀ V : ValuationSubring Ω, (∀ r : R, algebraMap R Ω r ∈ V) → a ∈ V) : IsIntegral R a := by
  apply GlobalTheory.CompanionTheory.Ar.Flat.isIntegral_of_forall_valuationSubring' <;> assumption

theorem mem_chartLatNm_of_forall_valuationSubring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (q : ℕ) (x : Ω),
    (∀ (c : (k : K) → ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ W : ValuationSubring Ω,
      (∀ p, y p / y ⟨p.1, c p.1⟩ ∈ W) → x * (u * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ q ∈ W) →
    x * u ^ q ∈ chartLatNm y a q := by
  intro K _ ι _ Ω _ y a u q x H c hc
  have e : x * u ^ q * ∏ k, y ⟨k, c k⟩ ^ (-((q : ℤ) * a k)) =
      x * (u * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ q := by
    rw [mul_pow, ← Finset.prod_pow, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  show x * u ^ q * ∏ k, y ⟨k, c k⟩ ^ (-((q : ℤ) * a k)) ∈ integralClosure (chartRingZ y c) Ω
  rw [e, mem_integralClosure_iff]
  refine isIntegral_of_forall_valuationSubring Subtype.val_injective _ fun V hV => H c hc V fun p => ?_
  exact hV ⟨_, Algebra.subset_adjoin ⟨p, rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.ChartVal
