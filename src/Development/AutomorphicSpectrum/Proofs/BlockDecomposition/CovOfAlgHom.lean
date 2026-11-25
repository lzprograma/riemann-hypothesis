module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.LinearAlgebra.TensorProduct.Associator

@[expose] public section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovMono

theorem cov_self (p : ℕ) (A : Type) [CommRing A] (r : ℕ → A) : Cov p r A := by
  intro K₁ K₀ _ _ _ _ _ _ d _ z hz k
  obtain ⟨w, hw⟩ := hz
  have key : z = d (TensorProduct.lid A K₁ w) := by
    have h1 : TensorProduct.lid A K₀ (d.lTensor A w) = d (TensorProduct.lid A K₁ w) :=
      LinearMap.congr_fun (show (TensorProduct.lid A K₀).toLinearMap ∘ₗ d.lTensor A =
        d ∘ₗ (TensorProduct.lid A K₁).toLinearMap from TensorProduct.ext' fun _ _ => by simp) w
    rw [hw] at h1
    simpa using h1
  rw [key, ← map_smul]
  exact ⟨_, rfl⟩

theorem cov_of_algHom (p : ℕ) (A : Type) [CommRing A] (r : ℕ → A)
    (B : Type) [CommRing B] [Algebra A B] (B₁ : Type) [CommRing B₁] [Algebra A B₁]
    (φ : B →ₐ[A] B₁) (h : Cov p r B₁) : Cov p r B := by
  intro K₁ K₀ _ _ _ _ hK₁ hK₀ d hd z hz k
  obtain ⟨w, hw⟩ := hz
  refine h K₁ K₀ hK₁ hK₀ d hd z ⟨φ.toLinearMap.rTensor K₁ w, ?_⟩ k
  have h1 :
      φ.toLinearMap.rTensor K₀ (d.lTensor B w) = d.lTensor B₁ (φ.toLinearMap.rTensor K₁ w) :=
    LinearMap.congr_fun ((LinearMap.rTensor_comp_lTensor (f := φ.toLinearMap) (g := d)).trans
      (LinearMap.lTensor_comp_rTensor (f := φ.toLinearMap) (g := d)).symm) w
  rw [← h1, hw]
  simp

theorem cov_mono : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Cov p r A ∧ ∀ (B : Type) [CommRing B] [Algebra A B] (B₁ : Type) [CommRing B₁] [Algebra A B₁] (φ : B →ₐ[A] B₁), Cov p r B₁ → Cov p r B := by
  intro p _ A _ r
  exact ⟨cov_self p A r, fun B _ _ B₁ _ _ φ h => cov_of_algHom p A r B B₁ φ h⟩

end GlobalTheory.CompanionTheory.CovMono
