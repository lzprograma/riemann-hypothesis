module

import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem

theorem host_cmData : ∀ (R : Ranks) (H : Host R), @CMData H.F H.E _ _ _ _ H.cmStar _ := by
  apply Formalism.BasicNotions.Examples₂.cmData

end GlobalTheory.Mem
