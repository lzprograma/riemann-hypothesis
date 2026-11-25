module

public import GroundTheory.GlobalFields.WeilGroups.QuasiCharacter
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section

open NumberField

namespace GroundTheory.Global

noncomputable section

namespace QuasiCharacter

variable {K : Type*} [Field K] [NumberField K]

def toUnitary (ψ : QuasiCharacter K) (h : ∀ c, ‖((ψ c : ℂˣ) : ℂ)‖ = 1) : HeckeCharacter K where
  toFun c := ⟨((ψ c : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (h c)⟩
  map_one' := Circle.ext (by simp)
  map_mul' c d := Circle.ext (by simp only [map_mul, Units.val_mul]; rfl)
  continuous_toFun := (Units.continuous_val.comp ψ.continuous).subtype_mk _


variable (ψ : QuasiCharacter K)

end QuasiCharacter

end

end GroundTheory.Global
