module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartLengthAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartResidueDegreeAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLength

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ChartLengthAlgClosed.proof (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartFinite.Statement) (h₄ : LengthFiniteAlgebra.Statement) (h₅ : ChartMaxIdeals.Statement)
    (h₆ : ChartLocalOrder.Statement) (h₇ : ChartResidueDegreeAlgClosed.Statement) :
    ChartLengthAlgClosed.Statement := by
  intro F _ _ n e I f t u q p _ hI hf hu hq hp hqt
  exact ChartLength.proof_of_residueDegree hI hf hu hq hp hqt h₂ h₃ h₄ h₅ h₆
    (fun W => h₇ F n e I W f t u q p hI hf hu hq hp hqt)

end

end GroundTheory.Heights₂.Heights
