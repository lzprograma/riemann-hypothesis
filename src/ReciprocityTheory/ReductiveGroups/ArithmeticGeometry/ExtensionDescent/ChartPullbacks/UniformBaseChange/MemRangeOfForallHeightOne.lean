module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.Out.KrullAlg

variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]

def denIdeal {ι : Type*} (x : ι → K) : Ideal A where
  carrier := {r | ∀ i, algebraMap A K r * x i ∈ (algebraMap A K).range}
  add_mem' ha hb i := let ⟨u, hu⟩ := ha i; let ⟨v, hv⟩ := hb i
    ⟨u + v, by rw [map_add (f := _), hu, hv, map_add (f := _), add_mul]⟩
  zero_mem' _ := ⟨0, by simp⟩
  smul_mem' c _ ha i := let ⟨u, hu⟩ := ha i; ⟨c * u, by rw [map_mul, hu, smul_eq_mul, map_mul, mul_assoc]⟩

lemma exists_assoc [IsNoetherianRing A] {ι : Type*} (x : ι → K)
    (hx : ∃ i, x i ∉ (algebraMap A K).range) :
    ∃ (d : A) (P : Ideal A), P.IsPrime ∧
      (∀ r, r ∈ P ↔ ∀ i, algebraMap A K r * (algebraMap A K d * x i) ∈ (algebraMap A K).range) ∧
      ∃ i, algebraMap A K d * x i ∉ (algebraMap A K).range := by
  classical
  have hne : (Ideal.Quotient.mk (denIdeal (A := A) x) 1) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    intro h; obtain ⟨i, hi⟩ := hx; exact hi (by simpa using h i)
  obtain ⟨P, hP, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hne
  rw [isAssociatedPrime_iff] at hP
  obtain ⟨hPp, y, hy⟩ := hP
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective y
  have key : ∀ r, r ∈ P ↔ ∀ i, algebraMap A K r * (algebraMap A K d * x i) ∈ (algebraMap A K).range := fun r => by
    rw [hy, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    show (∀ i, algebraMap A K (r * d) * x i ∈ (algebraMap A K).range) ↔ _
    simp only [map_mul, mul_assoc]
  refine ⟨d, P, hPp, key, ?_⟩
  by_contra hcon; apply hPp.ne_top; rw [Ideal.eq_top_iff_one, key 1]
  intro i; rw [(algebraMap A K).map_one, one_mul]; exact by_contra fun hi => hcon ⟨i, hi⟩

theorem exists_clear [IsNoetherianRing A] [IsIntegrallyClosed A] {ι : Type*} [Finite ι]
    (x : ι → K) (hx : ∃ i, x i ∉ (algebraMap A K).range) :
    ∃ P : Ideal A, P.IsPrime ∧ P.height = 1 ∧ ∃ b ∈ P,
      (∀ i, algebraMap A K b * x i ∈ (algebraMap A K).range) ∧
      ∃ i, ∃ u ∉ P, algebraMap A K u = algebraMap A K b * x i := by
  classical
  obtain ⟨d, P, hP, hPmem, i0, hi0⟩ := exists_assoc x hx
  obtain ⟨b0, hb0⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) (fun i => algebraMap A K d * x i)
  have hb0P : (b0 : A) ∈ P := (hPmem _).2 fun i => let ⟨y, hy⟩ := hb0 i; ⟨y, by rw [hy, Algebra.smul_def]⟩
  have hb0ne : (b0 : A) ≠ 0 := nonZeroDivisors.coe_ne_zero b0
  have hPne : P ≠ ⊥ := fun h => hb0ne (h ▸ hb0P |> (Submodule.mem_bot A).1)
  have hex : ∃ p ∈ P, ∃ u : A, algebraMap A K u = algebraMap A K p * (algebraMap A K d * x i0) ∧ u ∉ P := by
    by_contra hne; apply hi0
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hNne : N ≠ ⊥ := fun h => by
      have hm : algebraMap A K b0 ∈ N := (Submodule.mem_map).2 ⟨(b0 : A), hb0P, rfl⟩
      rw [h, Submodule.mem_bot] at hm
      exact hb0ne ((IsFractionRing.injective A K) (hm.trans (map_zero _).symm))
    have hint : IsIntegral A (algebraMap A K d * x i0) :=
      isIntegral_of_smul_mem_submodule N hNne ((IsNoetherian.noetherian P).map _) _ fun n hn => by
        obtain ⟨a, haP, rfl⟩ := (Submodule.mem_map).1 hn
        obtain ⟨u, hu⟩ := (hPmem a).1 haP i0
        exact (Submodule.mem_map).2 ⟨u, by_contra fun huP => hne ⟨a, haP, u, hu, huP⟩,
          by change algebraMap A K u = (algebraMap A K d * x i0) * algebraMap A K a; rw [hu, mul_comm]⟩
    exact IsIntegrallyClosed.isIntegral_iff.1 hint
  obtain ⟨p, hpP, u, hu, huP⟩ := hex
  refine ⟨P, hP, ?_, p * d, P.mul_mem_right d hpP,
    fun j => let ⟨v, hv⟩ := (hPmem p).1 hpP j; ⟨v, by rw [hv, (algebraMap A K).map_mul, mul_assoc]⟩,
    i0, u, huP, by rw [hu, (algebraMap A K).map_mul, mul_assoc]⟩
  have : Submodule.IsPrincipal (Ideal.span {p}) := ⟨⟨p, rfl⟩⟩
  have hmin : P ∈ (Ideal.span {p}).minimalPrimes :=
    ⟨⟨hP, (Ideal.span_singleton_le_iff_mem P).2 hpP⟩, fun Q hQ hQP q hq => by
      obtain ⟨v, hv⟩ := (hPmem q).1 hq i0
      have e : q * u = p * v := IsFractionRing.injective A K (by rw [map_mul, map_mul, hu, hv, mul_left_comm])
      exact (hQ.1.mem_or_mem (e ▸ Q.mul_mem_right v ((Ideal.span_singleton_le_iff_mem Q).1 hQ.2))).resolve_right
        fun h2 => huP (hQP h2)⟩
  exact le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin)
    (Order.one_le_iff_ne_zero.2 fun h => hPne (Ideal.height_eq_zero_iff_eq_bot.1 h))

theorem exists_height_one_not_mem [IsNoetherianRing A] [IsIntegrallyClosed A] (x : K)
    (hx : x ∉ (algebraMap A K).range) :
    ∃ P : Ideal A, P.IsPrime ∧ P.height = 1 ∧
      ∀ s ∉ P, algebraMap A K s * x ∉ (algebraMap A K).range := by
  obtain ⟨P, hP, h1, b, hbP, -, ⟨_, u, huP, hu⟩⟩ := exists_clear (A := A) (ι := Unit) (fun _ => x) ⟨(), hx⟩
  refine ⟨P, hP, h1, fun s hs ⟨a, ha⟩ => ?_⟩
  have e2 : s * u = b * a := IsFractionRing.injective A K (by rw [map_mul, map_mul, hu, ha, mul_left_comm])
  exact (hP.mem_or_mem (e2 ▸ P.mul_mem_right a hbP)).elim hs huP

theorem mem_range_of_forall_height_one [IsNoetherianRing A] [IsIntegrallyClosed A] (x : K)
    (h : ∀ P : Ideal A, P.IsPrime → P.height = 1 →
      ∃ s ∉ P, algebraMap A K s * x ∈ (algebraMap A K).range) :
    x ∈ (algebraMap A K).range := by
  by_contra hx
  obtain ⟨P, hP, h1, hs⟩ := exists_height_one_not_mem x hx
  obtain ⟨s, hsP, hsx⟩ := h P hP h1
  exact hs s hsP hsx

omit [IsFractionRing A K] in
theorem finite_height_one [IsNoetherianRing A] {a : A} (ha : a ≠ 0) :
    {P : Ideal A | P.IsPrime ∧ P.height = 1 ∧ a ∈ P}.Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})).subset fun _ ⟨_, h1, haP⟩ =>
    Ideal.mem_minimalPrimes_of_height_le ((Ideal.span_singleton_le_iff_mem _).2 haP) <|
      h1 ▸ Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha)

end ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
