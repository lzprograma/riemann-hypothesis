module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentColumnWhittakerTransformMirabolicInvari
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.unipotentColumnWhittakerTransform_mirabolic_invariant : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ) (f : GA E a → ℂ), m + 1 < a → Good ψ (m + 1) f → ∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, colT ψ (m + 1) f (ratGL E a γ * g) = colT ψ (m + 1) f g := by
  first | exact @GlobalTheory.CuspGeneric.colT_isMir_invariant
