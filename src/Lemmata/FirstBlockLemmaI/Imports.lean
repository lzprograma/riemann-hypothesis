module

public import Mathlib.RingTheory.Jacobson.Ideal

@[expose] public section

namespace Bl.FirstBlockLemmaI

theorem goal1 {R : Type} [CommRing R] {u z : R} :
  IsUnit u → z ∈ Ideal.jacobson ⊥ → IsUnit (u + z) := by
  intro hu hz
  obtain ⟨v, rfl⟩ := hu
  rw [Ideal.jacobson_bot] at hz
  have h : IsUnit (z * ↑v⁻¹ + 1) := (Ring.mem_jacobson_iff.mp hz) (↑v⁻¹ : R)
  have e : (v : R) + z = (z * ↑v⁻¹ + 1) * ↑v := by
    rw [add_mul, one_mul, mul_assoc, Units.inv_mul, mul_one, add_comm]
  rw [e]
  exact h.mul v.isUnit

end Bl.FirstBlockLemmaI
