module

public import Mathlib.NumberTheory.NumberField.Basic
import Lemmata.GeneralBFactThirdAlt.Imports

@[expose] public section

namespace Bl.general_b_fact_second_alt

theorem goal1 :
  ∀ {K : Type} [inst : Field.{0} K] [NumberField.{0} K] {r : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} K) (Fin r → K)) (v : Fin r → K),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} L)) v →
    Exists.{1} fun (a : NumberField.RingOfIntegers.{0} K) ↦
      And (Ne.{1} a 0) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} a v)) :=
  general_b_fact_third_alt.goal1

end Bl.general_b_fact_second_alt
