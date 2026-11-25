module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep

@[expose] public section



section
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct


namespace GlobalTheory.BigOn.Exp.SerBase
def KerOfAtAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => KerOf p w j
def TraceAt' : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => TraceOf p w j
def KernelRationalAt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => KerRat p w j
def LatticeInclusionAt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => LatIo p w j
def ReadComparisonAt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun _ _ _ _ p w j => ReadCmp p w j
end GlobalTheory.BigOn.Exp.SerBase
end
end
