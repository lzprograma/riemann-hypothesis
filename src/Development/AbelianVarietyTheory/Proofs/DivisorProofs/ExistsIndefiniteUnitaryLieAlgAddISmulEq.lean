module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
public import Formalism.LocalRingCardinality.DataTheta
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem upq_span (p q : ℕ) (Z : Mat p q) : ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  apply GlobalTheory.FockTensor.exists_upq_add

end GlobalTheory.HoweD
