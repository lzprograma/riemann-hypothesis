module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.VB.Cmp

variable {K Ω' : Type*} [Field K] [NumberField K] [Field Ω'] [Algebra K Ω'] (A : ValuationSubring Ω')

theorem val_le_one (x : 𝓞 K) : A.valuation (algebraMap K Ω' (x : K)) ≤ 1 := by
  have hv : A.valuation.Integers A :=
    ⟨Subtype.val_injective, fun a => A.valuation_le_one a,
      fun {r} hr => ⟨⟨r, A.mem_of_valuation_le_one r hr⟩, rfl⟩⟩
  have hx : IsIntegral ℤ (algebraMap K Ω' (x : K)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).algebraMap
  exact hv.isIntegral_iff_v_le_one.1 hx.tower_top

def ltIdeal : Ideal (𝓞 K) :=
  (IsLocalRing.maximalIdeal A).comap
    (((algebraMap K Ω').comp (algebraMap (𝓞 K) K)).codRestrict A.toSubring
      (fun x => A.mem_of_valuation_le_one _ (val_le_one A x)))

theorem mem_ltIdeal (x : 𝓞 K) : x ∈ ltIdeal (K := K) A ↔ A.valuation (algebraMap K Ω' (x : K)) < 1 :=
  A.valuation_lt_one_iff _

private theorem exists_placeOver_of_valuation_natCast_lt_one (n : ℕ) (hn : 0 < n) (h : A.valuation (n : Ω') < 1) :
    ∃ v : HeightOneSpectrum (𝓞 K), Formalism.ConjugateSelfDual.IsPlaceOver A v ∧
      ∀ x : 𝓞 K, x ∈ v.asIdeal ↔ A.valuation (algebraMap K Ω' (x : K)) < 1 := by
  have hprime : (ltIdeal (K := K) A).IsPrime := Ideal.comap_isPrime _ _
  have hmem : ((n : ℕ) : 𝓞 K) ∈ ltIdeal (K := K) A := by
    rw [mem_ltIdeal]
    simpa using h
  have hne : ((n : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨⟨ltIdeal (K := K) A, hprime, fun hbot => hne (Ideal.mem_bot.1 (hbot ▸ hmem))⟩,
    fun x => (mem_ltIdeal A x).symm, fun x => mem_ltIdeal A x⟩

theorem exists_over_above_iff (l : ℕ) [Fact l.Prime] :
    (∃ v : HeightOneSpectrum (𝓞 K), Formalism.ConjugateSelfDual.IsPlaceOver A v ∧ ((l : ℕ) : 𝓞 K) ∈ v.asIdeal) ↔
      A.valuation (l : Ω') < 1 := by
  constructor
  · rintro ⟨v, hv, hl⟩
    have h := (hv _).2 hl
    simpa using h
  · intro h
    obtain ⟨v, hv, hmem⟩ := exists_placeOver_of_valuation_natCast_lt_one (K := K) A l (Fact.out : l.Prime).pos h
    exact ⟨v, hv, (hmem _).2 (by simpa using h)⟩

end Formalism.VB.Cmp
