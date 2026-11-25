module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.LieOneComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneParam

@[expose] public section

open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Bor

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem level_lie (X : Lie E a) (φ : Sm E a) (h : IsOpen {k | act (.fin k) φ = φ}) :
    IsOpen {k | act (.fin k) (lie E a X φ) = lie E a X φ} := by
  apply _root_.level_lie <;> assumption

private theorem left_lie (X : Lie E a) (φ : Sm E a) (x : GA E a) (h : ∀ g, φ.1 (x * g) = φ.1 g) (g : GA E a) :
    (lie E a X φ).1 (x * g) = (lie E a X φ).1 g := by
  obtain ⟨c, c0, -, -, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  have h1 := hasDerivAt_curve φ (x * g) c X c0 cder
  have h2 := hasDerivAt_curve φ g c X c0 cder
  simp only [mul_assoc, h] at h1
  exact h1.unique h2

theorem UpperTheory.V.Lit.Geo.Pf.invLie :
    UpperTheory.V.Lit.Geo.Pf.InvLie := by
  intro E _ _ _ a φ h
  exact ⟨⟨ContAut.continuous_of_isOpen_stab E a φ h.level, h.left, h.centre⟩, fun X =>
    ⟨fun γ => left_lie X φ _ (h.left γ), fun t => left_lie X φ _ (h.centre t), level_lie X φ h.level⟩⟩

end
