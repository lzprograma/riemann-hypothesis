module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

@[expose] public section

theorem UpperTheory.Reformulated.B.Yhd1.mem_minimalPrimes_iff.{u_1} :
    ∀ {A : Type u_1} [CommRing A] [IsDomain A] [IsNoetherianRing A] {z : A},
      z ≠ (0 : A) → ∀ (W : Ideal A), W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = (1 : ℕ∞) ∧ z ∈ W := by
  intro A _ _ _ z hz W
  have hspan : 1 ≤ (Ideal.span {z}).height :=
    Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hz)
  constructor
  · intro hW
    exact ⟨hW.isPrime, le_antisymm
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hW)
      (hspan.trans (Ideal.height_mono hW.le)), hW.le (Ideal.mem_span_singleton_self z)⟩
  · rintro ⟨hP, hh, hzW⟩
    let := hP
    exact Ideal.mem_minimalPrimes_of_height_le
      ((Ideal.span_singleton_le_iff_mem W).mpr hzW) (hh.trans_le hspan)
