module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.LemB

def CjEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
  ∀ s : w.adicCompletion E →+* w.adicCompletion E,
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → s = cj w

def BcWeyl : Prop := ∀ (n : ℕ) (α α' : Fin (n / 2) → ℂˣ), GlobalTheory.LGrp.WeylConjU α α' →
  GlobalTheory.LGrp.bcParam n α = GlobalTheory.LGrp.bcParam n α'

end PositivityTheory.Rg.BcB.F.LemB

end
