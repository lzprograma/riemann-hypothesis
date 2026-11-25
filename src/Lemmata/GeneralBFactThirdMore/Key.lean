module

import Lemmata.NatMulIsIntegral.ExistsNatMulIsIntegral
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace Bl.general_b_fact_third'

theorem goal1 :
  ∀ {E : Type} [Field.{0} E] [NumberField.{0} E] {n : Nat}
  (L : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) (Fin n → E)),
  Eq.{1} (Submodule.span.{0, 0} E (SetLike.coe.{0, 0} L)) Top.top.{0} →
    ∀ (w : Fin n → E),
      Exists.{1} fun (m : Nat) ↦ And (LT.lt.{0} 0 m) (Membership.mem.{0, 0} L (HSMul.hSMul.{0, 0, 0} m w)) := by
  intro E _ _ n L hL w
  exact Bl.NatMulIsIntegral.goal1 (L := L) (z := w) (by rw [hL]; exact Submodule.mem_top)

end Bl.general_b_fact_third'
