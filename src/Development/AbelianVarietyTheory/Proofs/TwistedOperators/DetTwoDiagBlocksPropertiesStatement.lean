module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetTwoDiagBlocksProperties
import Formalism.LocalRingCardinality.DataHost
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDetInt
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct

theorem _root_.GlobalTheory.T.det_twoDiagBlocks_properties : ∀ (κ : Type) [CommRing κ] (n r t : ℕ) (hr : r ≤ n) (g : GL (Fin n) κ), (g ∈ blockTri (blk2 r) → Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) * dBlk (blk2 r) 1 g) ∧ (n = r + t → g ∈ blockTri (blkOf r t) → dBlk (blkOf r t) 1 g = dBlk (blk2 r) 1 g) ∧ (n = r → Matrix.GeneralLinearGroup.det (upperLeftBlock hr g) = Matrix.GeneralLinearGroup.det g) := by
  first | exact @GlobalTheory.VecInv.TwoBlockDet.det_blocks
