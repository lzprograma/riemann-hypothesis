module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.LocalRing

@[expose] public section

namespace GroundTheory.Variant₂.N1

open IsLocalRing

theorem exists_eq_unit_mul_pow_adicCompletion {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    {x : AdicCompletion (maximalIdeal R) R} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (AdicCompletion (maximalIdeal R) R)ˣ),
      x = ↑u * (algebraMap R (AdicCompletion (maximalIdeal R) R)) ϖ ^ n := by
  classical
  let A := AdicCompletion (maximalIdeal R) R
  have hex : ∃ k : ℕ, x ∉ maximalIdeal A ^ k := by
    by_contra! h
    exact hx <| IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := maximalIdeal A) (M := A)) x
      (fun k => by simpa only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.zero] using h k)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show Nat.find hex ≠ 0 by
    intro h
    exact Nat.find_spec hex (by rw [h, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top))
  have hM : maximalIdeal A = Ideal.span {algebraMap R A ϖ} := by
    rw [AdicCompletion.maximalIdeal_eq_map, congrArg (Ideal.map (algebraMap R A)) hϖ.maximalIdeal_eq,
      Ideal.map_span, Set.image_singleton]
  obtain ⟨y, hy⟩ : ∃ y : A, y * algebraMap R A ϖ ^ n = x := by
    rw [← Ideal.mem_span_singleton', ← Ideal.span_singleton_pow, ← hM]
    exact not_not.mp (Nat.find_min hex (show n < Nat.find hex by omega))
  suffices hu : IsUnit y by exact ⟨n, hu.unit, by rw [IsUnit.unit_spec, hy]⟩
  rw [← notMem_maximalIdeal, hM, Ideal.mem_span_singleton']
  rintro ⟨z, hz⟩
  apply Nat.find_spec hex
  rw [hn, hM, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  exact ⟨z, by rw [← hy, ← hz, pow_succ]; ring⟩

end GroundTheory.Variant₂.N1
