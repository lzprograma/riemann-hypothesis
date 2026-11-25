module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNontrivialDerivative

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem _root_.GlobalTheory.T.exists_nontrivial_derivative : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k m) V), IsSmooth τ → Nontrivial V → ∃ n ≤ m, Nontrivial (TwJacquet τ (derUnipM k m n) (derCharM k ψ m n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial | exact GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial | (intros; apply GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial <;> assumption)
