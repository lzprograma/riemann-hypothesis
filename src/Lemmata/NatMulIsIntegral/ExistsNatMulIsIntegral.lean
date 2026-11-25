module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.Submodule

@[expose] public section

namespace Bl.NatMulIsIntegral

theorem goal1 {E V : Type} [Field E] [NumberField E] [AddCommGroup V]
    [Module E V] [Module (NumberField.RingOfIntegers E) V]
    [IsScalarTower (NumberField.RingOfIntegers E) E V]
    {L : Submodule (NumberField.RingOfIntegers E) V} {z : V}
    (hz : z ∈ Submodule.span E (L : Set V)) :
    ∃ N : ℕ, 0 < N ∧ N • z ∈ L := by
  let M := Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers E) (nonZeroDivisors ℤ)
  obtain ⟨y, hy, s, hzs⟩ := (IsLocalization.mem_span_iff (M := M)).mp hz
  have hclear : (s : NumberField.RingOfIntegers E) • z = y := by
    rw [hzs, ← IsScalarTower.algebraMap_smul E, smul_smul, IsLocalization.mk'_spec' E 1 s,
      map_one, one_smul]
  obtain ⟨m, hm, he⟩ := s.property
  have hzL : m • z ∈ L := by
    rw [← Int.cast_smul_eq_zsmul (NumberField.RingOfIntegers E)]
    change (algebraMap ℤ (NumberField.RingOfIntegers E) m) • z ∈ L
    rw [he, hclear]
    simpa only [Submodule.span_eq] using hy
  refine ⟨m.natAbs, Int.natAbs_pos.mpr (nonZeroDivisors.ne_zero hm), ?_⟩
  rcases Int.natAbs_eq m with h | h
  · rwa [← natCast_zsmul, ← h]
  · rw [← natCast_zsmul, ← neg_neg (m.natAbs : ℤ), ← h, neg_smul]
    exact L.neg_mem hzL

end Bl.NatMulIsIntegral
