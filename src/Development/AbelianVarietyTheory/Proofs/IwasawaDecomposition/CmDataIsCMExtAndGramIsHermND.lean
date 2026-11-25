module

import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem hspace_gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) :
    W.gram.det ≠ 0 := by
  apply GlobalTheory.RecDict.det_gram_ne_zero

theorem cmData_isCMExt_and_gram_isHermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), IsCMExt F E cm.sig ∧ ∀ W : HSpace E, IsHermND cm.sig W.gram := by
  intro F E _ _ _ _ _ _ cm
  refine ⟨⟨cm.totReal, cm.cmUnram.1, cm.deg2, fun τ x => cm.cmUnram.2.1 τ x⟩, fun W => ⟨fun i j => ?_, hspace_gram_det_ne_zero W⟩⟩
  exact W.herm.eq (W.frame j) (W.frame i)

end GlobalTheory.Mem.Vol
