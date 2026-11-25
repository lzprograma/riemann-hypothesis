module

import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.ModelFunctionsMultiply
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTau
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HcParamGapGeIndex
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ}

def CkModel : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (m : Fin n → ℤ) (hm : NonnegDom ε m) (k : KG ε),
    cK (modelKType ε hm) k = ‖f0K ε m k‖

def CkTwist : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (c : ℤ),
    ∃ T' : KType ε (fun a => Λ a + (c : ℝ)), ∀ k, cK T' k = cK T k

def ModelFunctionsMultiply : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (m₁ m₂ : Fin n → ℤ), NonnegDom ε m₁ → NonnegDom ε m₂ → ∀ k : KG ε,
    f0K ε (m₁ + m₂) k = f0K ε m₁ k * f0K ε m₂ k

theorem coefPow_of (hM : CkModel) (hT : CkTwist) (hF : ModelFunctionsMultiply) : CoefPow := by
  apply CompanionTheory.RgFd.coefPow_of <;> assumption

end PositivityTheory.RgFd
