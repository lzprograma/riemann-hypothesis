module

import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDictMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open MeasureTheory Matrix

namespace GlobalTheory
open ValuativeRel

theorem norm_addChar_nonarch {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ0 : AddChar k ℂ) (hψ : Continuous ψ0) (t : k) : ‖ψ0 t‖ = 1 := by
  apply PositivityTheory.KCo.Mod.norm_one <;> assumption

theorem schr_unitary : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (μ : @Measure (κ → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (w : (κ → k) × (κ → k)) (φ φ' : (κ → k) → ℂ),
      ∫ y, GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ := by
  intro k _ _ _ _ _ ψ0 hψ κ _ μ hμ w φ φ'
  letI : MeasurableSpace (κ → k) := borel _
  haveI : BorelSpace (κ → k) := ⟨rfl⟩
  have h1 : ∀ s : k, ψ0 s * (starRingEnd ℂ) (ψ0 s) = 1 := fun s => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_addChar_nonarch ψ0 hψ s]; simp
  have h2 : (fun y => GlobalTheory.WeilM.schr ψ0 w φ y * (starRingEnd ℂ) (GlobalTheory.WeilM.schr ψ0 w φ' y)) =
      fun y => φ (y + w.1) * (starRingEnd ℂ) (φ' (y + w.1)) := by
    funext y
    simp only [GlobalTheory.WeilM.schr, map_mul]
    have := h1 (y ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2))
    linear_combination (φ (y + w.1) * (starRingEnd ℂ) (φ' (y + w.1))) * this
  rw [h2]
  exact integral_add_right_eq_self (fun y => φ y * (starRingEnd ℂ) (φ' y)) w.1

end GlobalTheory
