module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeq

@[expose] public section

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af Filter Asymptotics Function
open scoped MatrixGroups ModularForm Topology

private theorem fd_sturm {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (k : ℤ) :
    ∃ m : ℕ, ∀ f : CuspForm Γ k, (∀ n < m, (qExpansion 1 f).coeff n = 0) → f = 0 := by
  refine ⟨(k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1, fun f hf => ?_⟩
  have h1 := GlobalTheory.EisM.qExpansion_coeff_zero_of_isBigO_qParam_pow
    one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) _
    ((GlobalTheory.EisM.modularFormNorm_isBigO_self_atImInfty f).trans
      (GlobalTheory.EisM.isBigO_qParam_pow_of_qExpansion_coeff_zero hΓ f _ hf))
  have h2 : ModularForm.norm 𝒮ℒ f = 0 := by
    apply ModularForm.sturm_bound_levelOne
    refine lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)
    exact_mod_cast Nat.lt_succ_self _
  rw [ModularForm.norm_eq_zero_iff] at h2
  ext τ
  simpa using congr_fun h2 τ

theorem UpperTheory.V.Sd.finDim :
    UpperTheory.V.Sd.FinDim := by
  intro N k _
  have hΓ : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
    simp
  obtain ⟨m, hm⟩ := fd_sturm hΓ (k : ℤ)
  refine ⟨?_, fun f hf => hm f fun n _ => ?_⟩
  · let L : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)) (k : ℤ) →ₗ[ℂ]
        (Fin m → ℂ) :=
      { toFun := fun f i => (qExpansion 1 f).coeff i
        map_add' := fun f g => by
          ext i
          simp only [CuspForm.coe_add, ModularForm.qExpansion_add one_pos hΓ f g, map_add (f := _),
            Pi.add_apply]
        map_smul' := fun c f => by
          ext i
          simp only [CuspForm.coe_smul, ModularForm.qExpansion_smul one_pos hΓ c f,
            PowerSeries.coeff_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply] }
    refine Module.Finite.of_injective L fun f g hfg => ?_
    have hfg0 : f - g = 0 := hm (f - g) fun n hn => by
      have hc := congrFun hfg ⟨n, hn⟩
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at hc
      rw [CuspForm.coe_sub, ModularForm.qExpansion_sub one_pos hΓ f g, map_sub, hc, sub_self]
    exact sub_eq_zero.mp hfg0
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact CuspFormClass.qExpansion_coeff_zero f one_pos hΓ
    · exact hf n hn
