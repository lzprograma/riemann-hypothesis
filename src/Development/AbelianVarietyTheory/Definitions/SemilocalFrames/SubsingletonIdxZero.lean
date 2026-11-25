module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.NumberTheory.Height.NumberField
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

structure HRep (k r : ℕ) where
  H : Type
  [nG : NormedAddCommGroup H]
  [iP : InnerProductSpace ℂ H]
  σ : Mat k r → (H →L[ℂ] H)

attribute [instance] HRep.nG HRep.iP

variable {k r : ℕ}

namespace Ex

open scoped ContDiff

open scoped Matrix.Norms.Elementwise

end Ex

end GlobalTheory.Mom
