module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormLevelPrimesIsSplitSet
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



theorem _root_.GlobalTheory.T.rowFormLevelPrimes_isSplitSet : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → LevOf X I U L →
    ∀ t : TupU I U, Formalism.L2.DIV.IsSplitSet (LiftBrg.sgL X I U t) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.isSplitSet_sgL
