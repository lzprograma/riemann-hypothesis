module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm

open NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem zeta_pow_div {m n : ℕ} (hn : 0 < n) (h : m ∣ n) : zeta n ^ (n / m) = zeta m := by
  obtain ⟨k, rfl⟩ := h
  have hm : 0 < m := Nat.pos_of_mul_pos_right hn
  have hk : 0 < k := Nat.pos_of_mul_pos_left hn
  rw [Nat.mul_div_cancel_left k hm]
  unfold zeta
  rw [← Complex.exp_nat_mul]
  congr 1
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  push_cast
  field_simp

theorem KA_le {l l₂ : Level H} (h : l.Dvd l₂) : KA l ≤ KA l₂ := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  · have hz : zeta l₂.A ∈ IntermediateField.adjoin ℚ ({H.rt0, zeta l₂.A} : Set ℂ) :=
      IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    rw [SetLike.mem_coe, ← zeta_pow_div l₂.A_pos h.2.2]
    exact pow_mem hz _

end GlobalTheory.IndefiniteRowSideFullHecke.RelativeGroupHatForm
