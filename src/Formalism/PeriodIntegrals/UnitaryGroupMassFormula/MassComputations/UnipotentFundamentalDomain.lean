module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqOneOfToHAFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.EllipticCentralizerQuotientCompact
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

section Bridge

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem toInf_mul (s t : X.B.I.Ginf) : X.toInf hb (s * t) = X.toInf hb s * X.toInf hb t := by
  unfold HidaSetting.toInf
  rw [show ((s * t, 1) : X.B.I.GA) = (s, 1) * (t, 1) by simp, map_mul, map_mul]
  rfl

theorem split_toHA (hS : SplitIso) (p : X.B.I.GA) :
    splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p) = (X.toInf hb p.1, finHA X hb p.2) := by
  apply _root_.PI.AprimeInfU.split_toHA <;> assumption

theorem toInf_surjective (hS : SplitIso) : Function.Surjective (X.toInf hb) := by
  apply _root_.PI.AprimeInfU.toInf_surjective <;> assumption

end Bridge

end MassDataMassesW
