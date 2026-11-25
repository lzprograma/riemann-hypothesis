module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivativeValuationBounds

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

open Formalism.MainNotions.G

abbrev vecDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) : ℕ :=
  Formalism.MainNotions.CovariantDegrees.vecDeg LL S al

abbrev covDeg {ι : Type} {n : ℕ} (LL : Letters ι) (S : Set ι) (al : ι × Fin n →₀ ℕ) : ℕ :=
  Formalism.MainNotions.CovariantDegrees.covDeg LL S al

abbrev flt_L (A : Type*) [CommRing A] (e : ℤ) :=
  Formalism.MainNotions.G.GLWeightTheory.flt_L A e

alias flt_L_mem := Formalism.MainNotions.G.GLWeightTheory.flt_L_mem
alias flt_L_C := Formalism.MainNotions.G.GLWeightTheory.flt_L_C
alias T_mem_laurentFiltration := Formalism.MainNotions.G.GLWeightTheory.T_mem_laurentFiltration

abbrev flt_lift {B : Type*} [CommRing B] {σ : Type*}
    (Fl : Formalism.MainNotions.G.GLWeightTheory.flt_Fil B) (wt : (σ →₀ ℕ) →+ ℤ) :=
  Formalism.MainNotions.G.GLWeightTheory.flt_lift Fl wt

alias flt_lift_mem := Formalism.MainNotions.G.GLWeightTheory.flt_lift_mem
alias flt_monomial_mem := Formalism.MainNotions.G.GLWeightTheory.flt_monomial_mem
alias flt_C_mem := Formalism.MainNotions.G.GLWeightTheory.flt_C_mem
alias flt_pow_mem := Formalism.MainNotions.G.GLWeightTheory.flt_pow_mem
alias flt_hom_monomial := Formalism.MainNotions.G.GLWeightTheory.flt_hom_monomial
alias flt_hom_mem := Formalism.MainNotions.G.GLWeightTheory.flt_hom_mem

abbrev laurentCoeffFiltration (R : Type*) [CommRing R] (n : ℕ) (σ : Type*) (e : ℤ) :=
  Formalism.MainNotions.G.GLWeightTheory.laurentCoeffFiltration R n σ e

alias flt_mem_sDegs := Formalism.MainNotions.G.GLWeightTheory.flt_mem_sDegs
alias flt_le_valS := Formalism.MainNotions.G.GLWeightTheory.flt_le_valS
alias flt_lam1S_le := Formalism.MainNotions.G.GLWeightTheory.flt_lam1S_le
alias flt_valS_mul_ge := Formalism.MainNotions.G.GLWeightTheory.flt_valS_mul_ge

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
