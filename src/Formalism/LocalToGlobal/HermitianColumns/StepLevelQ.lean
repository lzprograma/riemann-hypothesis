module

public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel

@[expose] public section

noncomputable section

namespace Formalism.L2.Herm

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

structure StepLevelQ (hc : CMData F E) (S : HSpace E) (gp : Fin 2 → ℕ) (T f : ℕ)
    (Q : Finset (HeightOneSpectrum (𝓞 F))) where

  Lb : Submodule (𝓞 E) (Fin S.rank → E)
  Lb_fin : Module.Finite (𝓞 E) Lb
  Lb_int : Lb ≤ dualL hc S Lb
  Lb_dual : ∀ y ∈ dualL hc S Lb, (T : E) • y ∈ Lb

  Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F))
  Uloc_lev : ∀ v, Uloc v ≤ levelVL hc.sig S.gram v Lb
  Uloc_hyp : ∀ v : HeightOneSpectrum (𝓞 F), ((gp 0 : 𝓞 F) ∉ v.asIdeal) →
    ((gp 1 : 𝓞 F) ∉ v.asIdeal) → ((T : 𝓞 F) ∉ v.asIdeal) → v ∉ Q → Uloc v = levelVL hc.sig S.gram v Lb

  U : Subgroup (GL (Fin S.rank) (E ⊗[F] Af F))
  U_eq : ∀ x, x ∈ U ↔ x ∈ UAf hc S ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v

end Formalism.L2.Herm

end
