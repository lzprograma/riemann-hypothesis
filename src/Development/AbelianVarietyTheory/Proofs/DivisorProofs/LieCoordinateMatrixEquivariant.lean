module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
import Development.AbelianVarietyTheory.Definitions.Divisors.Tpr
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace GlobalTheory.WigAlg

theorem mul_embeddingScalar_eq_coord_mul {E : Type} [Field E] (τ : E →+* ℂ) (c : Cinf E) (z : ℂ) :
    c * atEmb τ z = atEmb τ (coord τ c * z) := by
  classical
  unfold coord atEmb
  funext w
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw
    split_ifs <;> simp
  · split_ifs <;> simp [Pi.single_eq_of_ne hw]

end GlobalTheory.WigAlg
