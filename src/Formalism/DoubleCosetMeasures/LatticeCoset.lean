module

public import Formalism.DoubleCosetMeasures.StatementV
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.ExistsContinuousLowerUpperEntry
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsIntOfLatOfLe
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.IsOpenIsIntSet
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LemmaU
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LowUniMulVecELast
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MeasureUniformizerMatrixSetMulCard
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MulInvBlockDiagApplySameBlock
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
public import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.TwoSided

@[expose] public section

namespace Formalism.DoubleCosetMeasures.Final

open Formalism.DoubleCosetMeasures

alias intTwoSided := _root_.Formalism.DoubleCosetMeasures.P.intTwoSided
alias simpleAdd := _root_.Formalism.DoubleCosetMeasures.P.simpleAdd
alias intInv := _root_.Formalism.DoubleCosetMeasures.P.intInv
theorem bbFinite : Formalism.DoubleCosetMeasures.BBFinite := Formalism.DoubleCosetMeasures.P.bbFinite_of intTwoSided intInv _root_.Formalism.DoubleCosetMeasures.P.isoInv simpleAdd
theorem bbNorm : Formalism.DoubleCosetMeasures.BBNorm := Formalism.DoubleCosetMeasures.P.bbNorm_of bbFinite
theorem phaseWellDef : Formalism.DoubleCosetMeasures.PhaseWellDef := Formalism.DoubleCosetMeasures.P.phaseWellDef
theorem glRed : Formalism.DoubleCosetMeasures.GLRed := Formalism.DoubleCosetMeasures.P.glRed
theorem volII : Formalism.DoubleCosetMeasures.VolII := Formalism.DoubleCosetMeasures.P.volII
theorem volJadd : Formalism.DoubleCosetMeasures.VolJadd := Formalism.DoubleCosetMeasures.P.volJadd

end Formalism.DoubleCosetMeasures.Final
