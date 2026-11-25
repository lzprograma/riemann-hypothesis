module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreserving

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.localConjugation_involutive_valuation_preserving : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
    (∀ x, cj w (cj w x) = x) ∧ ∀ x, Valued.v (cj w x) = Valued.v x := by
  first | exact @GlobalTheory.BCT.cj_involutive_valuation
