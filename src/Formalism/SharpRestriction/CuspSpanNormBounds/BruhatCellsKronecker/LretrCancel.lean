module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLiftDef
public import Lemmata.GeneralBFactRightAltForm.Imports

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat NumberField Module

section

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

theorem lretr_cancel (d : 𝓞 E) (hd : d ≠ 0) (x y : V) (h : d • x = d • y) : x = y := by
  have hdE : algebraMap (𝓞 E) E d ≠ 0 := by
    intro h0; exact hd ((FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h0, map_zero]))
  rw [← algebraMap_smul E d, ← algebraMap_smul E d] at h
  exact smul_right_injective V hdE h

end

theorem l_retr : IntegralRetraction := by
  intro E _ _ _ S Λ X hΛ
  obtain ⟨ρ, hρX, hρid⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract Λ hΛ.fg X
  let N : Submodule (𝓞 E) S.V := (LinearMap.ker ρ).map Λ.subtype
  let K : Submodule E S.V := Submodule.span E (N : Set S.V)
  -- Clearing denominators reduces disjointness to the integral kernel.
  have hK : Disjoint K X := by
    rw [Submodule.disjoint_def]
    intro x hxK hxX
    obtain ⟨d, hd, hdx⟩ := _root_.Bl.general_b_fact_right_alt_form.goal1 (N : Set S.V) x hxK
    have hdxN : d • x ∈ N := by
      simpa only [Submodule.span_eq] using hdx
    obtain ⟨n, hn, he⟩ := Submodule.mem_map.mp hdxN
    change (n : S.V) = d • x at he
    have hnX : (n : S.V) ∈ X := by
      rw [he, ← algebraMap_smul E d]
      exact X.smul_mem _ hxX
    have hn0 : n = 0 := (hρid n hnX).symm.trans (LinearMap.mem_ker.mp hn)
    apply lretr_cancel d hd
    simpa only [hn0, Submodule.coe_zero, smul_zero] using he.symm
  obtain ⟨Y, hKY, hYX⟩ := hK.exists_isCompl
  let P := X.projection Y hYX.symm
  refine ⟨P, fun _ hx => Submodule.projection_apply_of_mem_left hYX.symm hx,
    Submodule.projection_apply_mem hYX.symm, ?_⟩
  intro l hl
  let n : Λ := ⟨l, hl⟩
  have hρn : (ρ n : S.V) ∈ X := hρX n
  have hdiff : l - (ρ n : S.V) ∈ N := by
    apply Submodule.mem_map.mpr
    refine ⟨n - ρ n, LinearMap.mem_ker.mpr ?_, rfl⟩
    rw [map_sub, hρid (ρ n) hρn, sub_self]
  have hfix : P (ρ n : S.V) = (ρ n : S.V) :=
    Submodule.projection_apply_of_mem_left hYX.symm hρn
  have hzero : P (l - (ρ n : S.V)) = 0 :=
    Submodule.projection_apply_of_mem_right hYX.symm (hKY (Submodule.subset_span hdiff))
  rw [map_sub, hfix, sub_eq_zero] at hzero
  rw [hzero]
  exact (ρ n).property

end Formalism.MainNotions.BridgeLemma

end
