module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

def suppQ {D : D7} (v : FinPl D) {a b : ℕ} (r : ℕ) : Set (Matrix (Fin b) (Fin a) (Fv D.host.F v)) :=
  {x | IsUnit (topL r x).det ∧ Valued.v (topL r x).det = 1 ∧ (∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F) ∧
      ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1}

theorem phiQ_eq_zero_of_not_mem {D : D7} (v : FinPl D) {a b : ℕ} (r : ℕ) (mu : (Fv D.host.F v)ˣ →* ℂˣ)
    (x : Matrix (Fin b) (Fin a) (Fv D.host.F v)) (hx : x ∉ suppQ v r) : phiQ v r mu x = 0 := by
  unfold phiQ
  rw [dite_eq_right]
  exact hx

end GlobalTheory.NrmVol
