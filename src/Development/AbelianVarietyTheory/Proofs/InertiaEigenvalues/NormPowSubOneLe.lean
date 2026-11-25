module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormZpowSubOneLe
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

namespace GlobalTheory.CloseToUnitNorm

theorem norm_pow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (hu : ‖u‖ = 1) (n : ℕ) : ‖u ^ n - 1‖ ≤ ‖u - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : u ^ (n + 1) - 1 = u * (u ^ n - 1) + (u - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul, hu, one_mul]
    exact ih

theorem norm_zpow_sub_one_le {C : Type} [NormedField C] [IsUltrametricDist C] (u : C)
    (h : ‖u - (1 : C)‖ < (1 : ℝ)) (i : ℤ) : ‖u ^ i - (1 : C)‖ ≤ ‖u - (1 : C)‖ := by
  apply GlobalTheory.UnitNormPowerSubOne.norm_zpow_sub_one_le <;> assumption

end GlobalTheory.CloseToUnitNorm
