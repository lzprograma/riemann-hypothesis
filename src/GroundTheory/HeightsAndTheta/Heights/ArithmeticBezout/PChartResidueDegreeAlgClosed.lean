module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartResidueDegreeAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormBirationalAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsBis
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartResidueDegree

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

theorem ChartResidueDegreeAlgClosed.proof (h₁ : ChowFormBirationalAlgClosed.Statement) (h₂ : ChartFinite.Statement)
    (h₃ : ChartKernel.Statement) (h₄ : ConeDimOfChowForm.Statement) (h₅ : ConeDimComponent.Statement)
    (h₆ : ChowFormExists.Statement) (h₇ : IncidenceGeneric.Statement) (h₈ : ChartLocalOrder.Statement) :
    ChartResidueDegreeAlgClosed.Statement :=
  fun F _ _ n _ _ _ _ _ _ _ _ _ hI hf hu hq hp hqt hW hqW htW =>
    ChartResidueDegree.length_eq_one (h₁ F n) h₂ h₃ h₄ h₅ h₆ h₇ h₈ hI hf hu hq hp hqt hW hqW htW

end

end GroundTheory.Heights₂.Heights
