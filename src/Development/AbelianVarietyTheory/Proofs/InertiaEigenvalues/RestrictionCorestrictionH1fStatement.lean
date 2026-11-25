module

public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1f

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.restriction_corestriction_H1f : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LiftingTheory.adm20 D HW F := by
  first | exact @GlobalTheory.res_cor_H1f
