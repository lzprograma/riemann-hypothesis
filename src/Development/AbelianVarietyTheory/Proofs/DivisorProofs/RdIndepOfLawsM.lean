module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFDOf
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrameLaws
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct

namespace GlobalTheory



theorem rdIndep_of_lawsM : ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
    RdIndep (T.Q.Xo j) T.Q.c (T.U j) σ := by
  intro D T h j hj σ hσ
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.rdIndep_laws T.Q.c GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny GlobalTheory.abelianSchemeLaws_all.2.secTwist (T.U j) σ (h.evalWD j hj)
    (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ _ _ _ (T.Q.Xo j) T.Q.c)
    (h.unf j hj σ hσ)

end GlobalTheory
