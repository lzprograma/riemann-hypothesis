module

import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Mathlib.RingTheory.Ideal.Int

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.PlOver

open NumberField IsDedekindDomain

variable (D : D7)

theorem liesOver_of_mem {L : Type} [Field L] [NumberField L] {p : ℕ} [Fact p.Prime] (P : Ideal (𝓞 L)) [hP : P.IsPrime]
    (h : ((p : ℕ) : 𝓞 L) ∈ P) : P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have := Int.ideal_span_isMaximal_of_prime p
  refine ⟨?_⟩
  refine Ideal.IsMaximal.eq_of_le inferInstance ?_ ?_
  · exact (Ideal.IsPrime.under ℤ P).ne_top
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using h

theorem prime_unique {L : Type} [Field L] [NumberField L] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (P : Ideal (𝓞 L))
    [hP : P.IsPrime] (hp' : ((p : ℕ) : 𝓞 L) ∈ P) (hq' : ((q : ℕ) : 𝓞 L) ∈ P) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨a, b, hab⟩ := hc
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : 𝓞 L) = (a : 𝓞 L) * ((p : ℕ) : 𝓞 L) + (b : 𝓞 L) * ((q : ℕ) : 𝓞 L) := by
    have := congrArg (Int.cast : ℤ → 𝓞 L) hab.symm
    push_cast at this
    exact this
  rw [h1]
  exact P.add_mem (P.mul_mem_left _ hp') (P.mul_mem_left _ hq')

theorem resChar_mem (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  apply Formalism.MainNotions.J.resChar_mem

theorem resChar_eq_iff (p : ℕ) [hp : Fact p.Prime] (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = p ↔ ((p : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have := (D.plEq w).isPrime
  constructor
  · rintro rfl; exact resChar_mem D w
  · intro h; exact prime_unique (D.what₂.places.resChar_prime w) hp.out _ (resChar_mem D w) h

theorem span_ne_bot (p : ℕ) [hp : Fact p.Prime] : Ideal.span {(p : ℤ)} ≠ ⊥ := by
  simp [hp.out.ne_zero]

theorem exists_over (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 D.what₂.LL))
    (hP : P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 D.what₂.LL)) :
    ∃ w : {w : D.what₂.places.Pl // D.what₂.places.resChar w = p}, (D.plEq w.1).asIdeal = P := by
  obtain ⟨hPp, hPl⟩ := hP
  have hb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (span_ne_bot p) P
  refine ⟨⟨D.plEq.symm ⟨P, hPp, hb⟩, ?_⟩, by simp⟩
  rw [resChar_eq_iff]
  simpa using Formalism.MainNotions.J.mem_of_liesOver (p := p) P

theorem plNe (p : ℕ) [Fact p.Prime] : Nonempty {w : D.what₂.places.Pl // D.what₂.places.resChar w = p} := by
  have := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨P, hP⟩ := Ideal.nonempty_primesOver (S := 𝓞 D.what₂.LL) (Ideal.span {(p : ℤ)})
  exact ⟨(exists_over D p P hP).choose⟩

end Formalism.BasicNotions.Examples₂.PlOver
