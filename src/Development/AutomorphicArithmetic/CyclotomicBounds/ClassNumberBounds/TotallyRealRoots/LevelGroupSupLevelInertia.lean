module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LeNuIffPowMemPrinc
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop
public import Mathlib.FieldTheory.Finite.Basic
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.UnitsMapSurjOfZmod

@[expose] public section

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem lv_princ_le (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    princ l (N.factorization l) ≤ levelGroup l N H := by
  intro u hu
  refine mem_levelGroup.mpr ⟨1, H.one_mem, ?_⟩
  rw [map_one]
  exact (MonoidHom.mem_ker.mp hu).symm

theorem princ_le_levelGroup (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    princ l (N.factorization l) ≤ levelGroup l N H ∧ IsOpen (levelGroup l N H : Set ℤ_[l]ˣ) :=
  ⟨lv_princ_le N H, Subgroup.isOpen_mono (lv_princ_le N H) (isOpen_princ _)⟩

theorem levelGroup_eq_top {N : ℕ} (hN : ¬ l ∣ N) (H : Subgroup (ZMod N)ˣ) :
    levelGroup l N H = ⊤ ∧ resOrder l (levelGroup l N H) = l - 1 := by
  have h : levelGroup l N H = ⊤ := by
    rw [eq_top_iff]
    intro u _
    apply lv_princ_le N H
    rw [mem_princ, Nat.factorization_eq_zero_of_not_dvd hN, pow_zero]
    exact one_dvd _
  refine ⟨h, ?_⟩
  rw [h, resOrder, Subgroup.map_top_of_surjective _ _root_.KStar.TotallyRealRoots.red_surjective, Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units]

end KStar.TotallyRealRoots
