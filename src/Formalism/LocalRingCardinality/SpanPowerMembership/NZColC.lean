module

public import Mathlib.Basic.Complex.Basic
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.SpanPowerMembership.ClassRecordRowDimensionZero

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] [DecidableEq ι]

variable {K ι} (σ : K →+* ℂ)

abbrev FK (ι : Type) : Type := ι → Unit → ℂ

end Std

end Formalism.BasicNotions.Examples₂.NZ
