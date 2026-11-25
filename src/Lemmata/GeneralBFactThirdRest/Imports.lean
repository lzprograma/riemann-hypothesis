module

public import Formalism.LocalRingCardinality.DataSpaces
import Lemmata.GeneralBFactLeftAlt.Imports

@[expose] public section

namespace Bl.general_b_fact_third''''

theorem goal1 :
  ∀ {E : Type} [Field.{0} E] [NumberField.{0} E] [StarRing.{0} E] (S : Formalism.BasicNotions.HSpace E)
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) S.V),
  Submodule.IsFullLattice.{0, 0, 0} E Λ →
    ∀ (x : S.V),
      Exists.{1} fun (a : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} a 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} a x)) :=
  @general_b_fact_left_alt.goal1

end Bl.general_b_fact_third''''
