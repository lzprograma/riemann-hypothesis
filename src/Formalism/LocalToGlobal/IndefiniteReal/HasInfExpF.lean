module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Tactic.TypeStar
import Formalism.LocalToGlobal.IndefiniteReal.DatumF

@[expose] public section

noncomputable section

open MeasureTheory

namespace Formalism.IndefR.LiftF

section Kernels

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF IsDedekindDomain NumberField
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  {Tau : Type} [Fintype Tau] (tauE : Tau → (E →+* ℂ)) (xi0 : E)


variable (F) in
def intAfF : Set (Af F) := {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}


variable (F E) in
def intAEF : AddSubgroup (Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAfF F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}

end Kernels

end Formalism.IndefR.LiftF

end
