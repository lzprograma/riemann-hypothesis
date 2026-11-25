module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CthFac
public import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem sg_ne_zero : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → sg c x τ ≠ 0 :=
  fun _ _ τ h => (GlobalTheory.Sieg.Model.multipliable_and_sg_ne_zero h τ).2.2

end GlobalTheory.Sieg
