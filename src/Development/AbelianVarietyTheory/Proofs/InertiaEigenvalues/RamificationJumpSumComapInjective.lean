module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_comap_injective :
    ∀ (G G' : Type) [Group G] [Group G'] (j : G' →* G) (R : ℕ → Subgroup G) (B : Subgroup G), Function.Injective j →
      jumpSum (fun t => (R t).comap j) ⊤ (B.comap j) = jumpSum R j.range B := by
  intro G G' _ _ j R B hj
  unfold jumpSum
  apply finsum_congr
  intro t
  have h1 : (⊤ ⊓ (R t).comap j ≤ B.comap j) ↔ (j.range ⊓ R t ≤ B) := by
    rw [top_inf_eq]
    constructor
    · rintro h x ⟨⟨y, rfl⟩, hy⟩
      exact h (show y ∈ (R t).comap j from hy)
    · intro h y hy
      exact h ⟨⟨y, rfl⟩, hy⟩
  have h2 : Nat.card ↥(⊤ ⊓ (R t).comap j) = Nat.card ↥(j.range ⊓ R t) := by
    rw [top_inf_eq, ← Subgroup.map_comap_eq, Subgroup.card_map_of_injective hj]
  rw [h2]
  by_cases h : j.range ⊓ R t ≤ B
  · rw [ite_eq_left (h1.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (h1.mp h')), ite_eq_right h]

end GlobalTheory.PMon.Ram
