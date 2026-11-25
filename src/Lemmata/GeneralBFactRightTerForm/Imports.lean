module

public import Mathlib.NumberTheory.NumberField.Basic
import Lemmata.FirstBlockLemmaE.Imports

@[expose] public section

namespace Bl.general_b_fact_right_ter_form

open NumberField

open scoped Pointwise in
theorem goal1 {L : Type} [Field L] [NumberField L] (x : L) (c : ℤ)
    (hx : x ^ 2 = ((4 * (2 * c) + 1 : ℤ) : L))
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [P.LiesOver (Ideal.span {(2 : ℤ)})]
    (σ : Gal(L/ℚ)) (hσ : σ ∈ MulAction.stabilizer (Gal(L/ℚ)) P) : σ x = x := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [← map_pow, hx, map_intCast] : (σ x) ^ 2 = x ^ 2) with h | h
  · exact h
  exfalso
  obtain ⟨y, hy, hyy⟩ := Bl.FirstBlockLemmaE.goal1 ((1 + x) / 2) (2 * c)
    (by push_cast; linear_combination (by rw [hx]; push_cast; ring : x ^ 2 = 8 * (c : L) + 1) / 4)
  have h2 : (2 : 𝓞 L) ∈ P := by
    simpa using (Ideal.mem_of_liesOver P (Ideal.span {(2 : ℤ)}) (2 : ℤ)).mp (Ideal.subset_span rfl)
  have hmem : y * (y - 1) ∈ P := by
    rw [show y * (y - 1) = 2 * (c : 𝓞 L) by push_cast at hyy; linear_combination hyy]
    exact P.mul_mem_right _ h2
  have key : ∀ a ∈ P, σ • a ∈ P := fun a ha =>
    hσ ▸ Ideal.mem_map_of_mem (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (𝓞 L) σ) ha
  have hσy : σ • y = 1 - y := NumberField.RingOfIntegers.ext <| by
    change σ (y : L) = ((1 - y : 𝓞 L) : L)
    push_cast; simp only [hy, map_div₀, map_add, map_one, h, map_ofNat]; ring
  have h1 : (1 : 𝓞 L) ∈ P := by
    rcases hP.mem_or_mem hmem with h' | h'
    · rw [show (1 : 𝓞 L) = (1 - y) + y by ring]
      exact P.add_mem (hσy ▸ key y h') h'
    · have h4 := key _ h'; rw [smul_sub, hσy, smul_one] at h4
      rw [show (1 : 𝓞 L) = -((1 - y - 1) + (y - 1)) by ring]
      exact P.neg_mem (P.add_mem h4 h')
  exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)

end Bl.general_b_fact_right_ter_form
