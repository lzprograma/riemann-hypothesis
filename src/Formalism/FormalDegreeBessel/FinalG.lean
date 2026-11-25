module

public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GNonneg
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

@[expose] public section

namespace Formalism.QuantumDeterminants

theorem uHGroup : UHGroup := unitary_group_holds
theorem uHConj : UHConj := unitary_conjugation_holds
theorem hpkFacts : HpkFacts := hermitian_pos_facts_hold
theorem nSubgroup : NSubgroup := unipotent_subgroup_holds
theorem ellAdd : EllAdd := length_additive_holds
theorem psiChar : PsiChar := additive_character_holds
theorem uWNormal : UWNormal := unitary_weyl_normal_holds
theorem sGroup : SGroup := symmetric_group_holds
theorem dInv : DInv := diagonal_inverse_holds
theorem gInv : GInv := group_inverse_holds
alias gFactor := _root_.Formalism.QuantumDeterminants.group_factorization_holds
alias revCS := _root_.Formalism.QuantumDeterminants.reverse_cauchy_schwarz_holds
alias gGram := _root_.Formalism.QuantumDeterminants.group_gram_holds
theorem gNonneg : GNonneg := gNonneg_of group_gram_holds

end Formalism.QuantumDeterminants
