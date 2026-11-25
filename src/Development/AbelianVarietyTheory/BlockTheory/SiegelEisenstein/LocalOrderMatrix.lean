module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Formalism.LocalRingCardinality.Params
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Divisibility.CoefMod

@[expose] public section

open MeasureTheory ValuativeRel Matrix NumberField IsDedekindDomain

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix
open GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SymChain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

def ordX (R : Ranks) (j : ℕ) : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j) :=
  ((finSumFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by unfold Ranks.N; ring))

theorem ordX_d (R : Ranks) (j : ℕ) (i : Fin j) (l : Fin R.t) :
    (ordX R j (.inr (i, l))).val = R.k + j + (l.val + R.t * i.val) := rfl

end GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix
