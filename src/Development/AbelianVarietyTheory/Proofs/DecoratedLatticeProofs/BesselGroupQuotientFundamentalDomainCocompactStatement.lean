module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompact
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical

theorem _root_.GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ), B.μR.IsHaarMeasure ∧ IsClosed (besGrp B.d B.o : Set (GA D B.V)) ∧ (∃ Ω : Set (GA D B.V), IsCompact Ω ∧ ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω) ∧ ∃ 𝓢 : Set (besGrp B.d B.o), IsFundamentalDomain ((GQ B.V).subgroupOf (besGrp B.d B.o)) 𝓢 B.μR ∧ B.μR 𝓢 < ⊤ ∧ ∀ F : GA D B.V → ℂ, ContinuousOn F (besGrp B.d B.o : Set (GA D B.V)) → (∀ γ ∈ GQ B.V ⊓ besGrp B.d B.o, ∀ s ∈ besGrp B.d B.o, F (γ * s) = F s) → IntegrableOn (fun s : besGrp B.d B.o => F s) 𝓢 B.μR ∧ ∫ s in 𝓢, F s ∂B.μR = ∫ a in B.vA.𝓕, ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν ∂B.vA.μ := by
  exact @GlobalTheory.BesselQuot.besGrp_quotient
