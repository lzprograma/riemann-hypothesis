module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupDivEqMulDivMulInvDiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjQuotNsUnitsEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

theorem _root_.GlobalTheory.T.conjQuot_eq_one_of_mem_nsUnits_of_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), GlobalTheory.UnitaryBC.IsSplitAt w →
    ∀ u ∈ GlobalTheory.MuExist.nsUnits E, GlobalTheory.ConsEta.conjQuot E w u = 1 := by
  first | exact @GlobalTheory.ConsEta.conjQuot_nsUnits_eq_one
