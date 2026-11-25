module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLatticeChainLatAndComap
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

namespace Bl.general_b_fact_left_ter_form

theorem goal1 :
  ∀ {R K V : Type} [CommRing.{0} R] [IsDomain.{0} R] [Field.{0} K] [Algebra.{0, 0} R K]
  [IsFractionRing.{0, 0} R K] [AddCommGroup.{0} V] [Module.{0, 0} R V] [Module.{0, 0} K V]
  [IsScalarTower.{0, 0, 0} R K V] (M : Submodule.{0, 0} R V) (y : V),
  Membership.mem.{0, 0} (Submodule.span.{0, 0} K (SetLike.coe.{0, 0} M)) y →
    Exists.{1} fun (s : R) ↦ And (Ne.{1} s 0) (Membership.mem.{0, 0} M (HSMul.hSMul.{0, 0, 0} s y)) := by
  apply GlobalTheory.RootEx.ChainLattice.exists_smul_mem

end Bl.general_b_fact_left_ter_form
