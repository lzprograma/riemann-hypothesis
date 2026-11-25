module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)

theorem _root_.GlobalTheory.T.harmonic_polynomial_eq_zero_of_function : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → ∀ P ∈ harm m w B, harmFn m w B P = 0 → P = 0 := by
  first | exact @GlobalTheory.ExportSeries.HarmInj.harm_inj
