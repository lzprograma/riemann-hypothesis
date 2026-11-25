module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.TorusFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ModelLat
public import Mathlib.NumberTheory.NumberField.Discriminant.Different

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj
open scoped Pointwise

theorem absNorm_smul_eq {E : Type} [Field E] [NumberField E] (σ : E ≃ₐ[ℚ] E) (I : Ideal (𝓞 E)) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (σ • I) (MulSemiringAction.toRingEquiv _ _ σ)
    (by rw [Ideal.pointwise_smul_def]; rfl)).toEquiv).symm

theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  apply ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTorusFrame.finrank_eq

end ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI
