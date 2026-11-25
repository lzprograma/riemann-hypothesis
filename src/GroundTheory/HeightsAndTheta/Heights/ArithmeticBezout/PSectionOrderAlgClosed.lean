module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionOrderAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartChoiceAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartLengthAlgClosed
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSpecFirst
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartLength
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem SectionOrderAlgClosed.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : ChartChoiceAlgClosed.Statement) (h₄ : Vertical.SpecFirstNeField.Statement)
    (h₅ : LocalizationPrimeDVR.Statement) (h₆ : EmultiplicityOrd.Statement) (h₇ : ChartFinite.Statement)
    (h₈ : ChartLocDomain.Statement) (h₉ : ChartNormAlgClosed.Statement)
    (h₁₀ : ChartLengthAlgClosed.Statement) (h₁₁ : LengthQuotientDet.Statement) :
    SectionOrderAlgClosed.Statement := by
  intro F _ _ n e I f u hI hf hu
  exact SectionOrder.proof_of_chart hI hf hu h₁ h₂ (fun q => h₃ F n e I f q hI hf)
    (h₄ F n e I f u hI hf hu) h₅ h₆ h₇ h₈ (fun t p _ h htp => h₉ F n e I f t p hI hf h htp u)
    (fun t q p _ => h₁₀ F n e I f t u q p hI hf hu) h₁₁

end

end GroundTheory.Heights₂.Heights
