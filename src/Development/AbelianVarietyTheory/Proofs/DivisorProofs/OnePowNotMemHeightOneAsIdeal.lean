module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsTopGrid

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

namespace GlobalTheory.WtInterlaceC

open Finset GlobalTheory.SignedHC GlobalTheory.FunObj GlobalTheory.ChiGrid

theorem weights_top_grid : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (τ : D.what₂.Tau),
    Formalism.L2.Col.Br.Interlace G.sp.topDec.rank.symm (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ) ∧
      Formalism.L2.Col.Br.SameShift (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ) :=
  GlobalTheory.WtInterlace.weights_top_grid

end GlobalTheory.WtInterlaceC
