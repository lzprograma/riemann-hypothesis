module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula

theorem _root_.GlobalTheory.T.schwartz_bound_finite_infinite : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (Φ : Mx D m n → ℂ), Φ ∈ schwartzA θ m n → Continuous Φ ∧ ∃ (k : ℕ) (f : Fin k → SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ) (g : Fin k → (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ), (∀ i, g i ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) ∧ ∀ x, ‖Φ x‖ₑ ≤ ∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ := by
  first | exact @GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated
