module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixModularFormGamma1InterGam
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Mathlib.Tactic.Linter.Style

@[expose] public section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem conj_mem_lev {N l : ℕ} {d : ℤ} {σ : SL(2, ℤ)} (hσ : IsDia N l d σ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ lev N l) : σ * γ * σ⁻¹ ∈ lev N l := by
  apply GlobalTheory.Hk.dia_conj_mem <;> assumption

end GlobalTheory.Hk

namespace GlobalTheory.Hk


open scoped Pointwise in
theorem dia_cuspForm : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ →
    ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∃ g : CuspForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.dia k σ ⇑f := by
  intro N l k d σ _ hσ f
  have hle : ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ) •
      (lev N l : Subgroup (GL (Fin 2) ℝ)) ≤ (lev N l : Subgroup (GL (Fin 2) ℝ)) := by
    intro y hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
      ConjAct.toConjAct_smul, inv_inv] at hy
    obtain ⟨γ, hγ, hγe⟩ := hy
    refine ⟨σ * γ * σ⁻¹, conj_mem_lev hσ hγ, ?_⟩
    change Matrix.SpecialLinearGroup.mapGL ℝ (σ * γ * σ⁻¹) = y
    rw [map_mul, map_mul, map_inv, hγe]
    group
  refine ⟨{ toFun := dia k σ f
            slash_action_eq' := fun A hA => ?_
            holo' := ?_
            zero_at_cusps' := fun {x} hx => ?_ }, rfl⟩
  · obtain ⟨γ, hγ, rfl⟩ := hA
    have h : (f : ℍ → ℂ) ∣[k] (σ * γ * σ⁻¹) = f :=
      f.slash_action_eq' _ ⟨σ * γ * σ⁻¹, conj_mem_lev hσ hγ, rfl⟩
    show ((f : ℍ → ℂ) ∣[k] σ) ∣[k] γ = (f : ℍ → ℂ) ∣[k] σ
    rw [← SlashAction.slash_mul]
    have e : σ * γ = (σ * γ * σ⁻¹) * σ := by group
    rw [e, SlashAction.slash_mul, h]
  · exact MDifferentiable.slash f.holo' _ _
  · have h3 : IsCusp (Matrix.SpecialLinearGroup.mapGL ℝ σ • x) (lev N l : Subgroup (GL (Fin 2) ℝ)) :=
      (hx.smul _).mono hle
    show x.IsZeroAt ((f : ℍ → ℂ) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ σ) k
    exact OnePoint.IsZeroAt.smul_iff.1 (f.zero_at_cusps' h3)

end GlobalTheory.Hk
