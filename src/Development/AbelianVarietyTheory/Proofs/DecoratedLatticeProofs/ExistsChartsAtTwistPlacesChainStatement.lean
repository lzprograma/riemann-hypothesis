module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartsAtTwistPlacesChain
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

theorem _root_.GlobalTheory.T.exists_charts_at_twist_places_chain : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, (∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP) ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → (∃ e, IsIdemOf φ e) ∧ (∃ x ϖ, IsLocUnif φ x ϖ) ∧ (∃ ι, IsChart s j φ ι) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : (Fv D.host.F v)ˣ →* ℂˣ, GlobalTheory.SmGL.IsUnitaryChar μ ∧ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) := by
  first | exact @GlobalTheory.TwistChart.charts_at_twist
