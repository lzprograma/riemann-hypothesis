module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinprodNonsplitSignTotallyPositiveEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.finprod_nonsplit_sign_totallyPositive_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ S : Set (Pl E), IsSection S → ∀ d : E, d ≠ 0 → (∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ d = r) → ∏ᶠ w ∈ S, (if IsSplitAt w then (1 : ℂ) else (-1) ^ ordL (algebraMap E (w.adicCompletion E) d)) = 1 := by
  first | exact @GlobalTheory.UnitaryClasses.signProd_totPos
