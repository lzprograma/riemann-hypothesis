module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.GraphTransport4
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

@[expose] public section

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section Parts

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem isomD_iffG {g : SplitG M.L} {t₁ t₂ : Term V M r} (hg₁ : GoodG H g t₁) (hg₂ : GoodG H g t₂)
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) :
    IsomD H t₁ t₂ θ ↔ ∀ Y W Y₂ W₂ : Ix r → M.L.O,
      PsiG H hg₂ (θ ((PsiG H hg₁).symm (Submodule.Quotient.mk Y))) = Submodule.Quotient.mk Y₂ →
      PsiG H hg₂ (θ ((PsiG H hg₁).symm (Submodule.Quotient.mk W))) = Submodule.Quotient.mk W₂ →
      formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t₂.f t₂.f')
          (algebraMap F E t₂.T) (algebraMap F E t₂.T') Y₂ W₂ -
        formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t₁.f t₁.f')
          (algebraMap F E t₁.T) (algebraMap F E t₁.T') Y W ∈ M.L.O := by
  constructor
  · intro hI Y W Y₂ W₂ h1 h2
    rw [PsiG_symm_mk] at h1 h2
    have e1 : θ (ddMk H t₁ ((sharpEquiv H t₁ (unit_gramHG H hg₁)).symm Y)) =
        ddMk H t₂ ((sharpEquiv H t₂ (unit_gramHG H hg₂)).symm Y₂) := by
      rw [← PsiG_symm_mk H hg₂, ← h1, LinearEquiv.symm_apply_apply]
    have e2 : θ (ddMk H t₁ ((sharpEquiv H t₁ (unit_gramHG H hg₁)).symm W)) =
        ddMk H t₂ ((sharpEquiv H t₂ (unit_gramHG H hg₂)).symm W₂) := by
      rw [← PsiG_symm_mk H hg₂, ← h2, LinearEquiv.symm_apply_apply]
    have k := hI _ _ _ _ e1 e2
    rw [h_eq_formG H hg₂, h_eq_formG H hg₁] at k
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply] at k
    exact k
  · intro hI x y x₂ y₂ h1 h2
    have k1 : PsiG H hg₂ (θ ((PsiG H hg₁).symm
        (Submodule.Quotient.mk (sharpEquiv H t₁ (unit_gramHG H hg₁) x)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramHG H hg₂) x₂) := by
      rw [PsiG_symm_mk, LinearEquiv.symm_apply_apply, h1, PsiG_mk]
    have k2 : PsiG H hg₂ (θ ((PsiG H hg₁).symm
        (Submodule.Quotient.mk (sharpEquiv H t₁ (unit_gramHG H hg₁) y)))) =
        Submodule.Quotient.mk (sharpEquiv H t₂ (unit_gramHG H hg₂) y₂) := by
      rw [PsiG_symm_mk, LinearEquiv.symm_apply_apply, h2, PsiG_mk]
    have k := hI _ _ _ _ k1 k2
    rw [h_eq_formG H hg₂ x₂ y₂, h_eq_formG H hg₁ x y]
    exact k

end Parts

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
