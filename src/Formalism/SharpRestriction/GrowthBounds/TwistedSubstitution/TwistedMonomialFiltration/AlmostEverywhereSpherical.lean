module

public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TMemLaurentFiltration

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

open Formalism.MainNotions.G

alias flt_twistMat_mem := Formalism.MainNotions.G.GLWeightTheory.flt_twistMat_mem

abbrev flt_cost {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (b : Bool) : (ι × Fin n →₀ ℕ) →+ ℤ :=
  Formalism.MainNotions.G.GLWeightTheory.flt_cost LL S b

alias flt_cost_single := Formalism.MainNotions.G.GLWeightTheory.flt_cost_single

abbrev flt_compat (e : ℤ) (bm : Bool) : Prop :=
  Formalism.MainNotions.G.GLWeightTheory.flt_compat e bm

alias flt_twistX_mem := Formalism.MainNotions.G.GLWeightTheory.flt_twistX_mem
alias flt_twist_monomial_mem := Formalism.MainNotions.G.GLWeightTheory.flt_twist_monomial_mem
alias flt_gL_mul_gLinv := Formalism.MainNotions.G.GLWeightTheory.flt_gL_mul_gLinv
alias flt_gLinv_mul_gL := Formalism.MainNotions.G.GLWeightTheory.flt_gLinv_mul_gL
alias flt_twistMat_mul := Formalism.MainNotions.G.GLWeightTheory.flt_twistMat_mul

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
