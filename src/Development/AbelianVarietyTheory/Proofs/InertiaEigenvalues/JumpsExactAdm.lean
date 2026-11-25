module

public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJumpVIffOfExactCrystallineLattices

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem jumps_exact_adm : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F ∧ Formalism.MainNotions.LiftingTheory.adm23 D HW F := by
  intro D HW F
  exact ⟨fun l _ K LL => _root_.GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat l (D.loc l) (D.locA l) (D.locT l) K LL,
    fun l _ K LL => _root_.GlobalTheory.Per.SESJumps.isJumpV_iff_of_isSESLat l (D.loc l) (D.locA l) (D.locT l) K LL⟩

end GlobalTheory
