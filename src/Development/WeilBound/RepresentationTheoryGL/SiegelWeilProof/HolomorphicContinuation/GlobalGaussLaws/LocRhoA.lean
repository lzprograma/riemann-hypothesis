module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulasStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFockVectorOfSchrodingerMemFockSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhatStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerFunctionFockVectorPolynomialGaussianStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEta

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.RhoH

theorem fock_stable : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s → ∀ k ∈ K D n, (ω k Φ).1 ∈ fockA θ V n l s :=
  _root_.GlobalTheory.CompanionTheory.ThTot.weil_fock_mem

theorem l_ne_zero : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ τ, l τ ≠ 0 := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl τ h0
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  have h := habs τ
  rw [h0, abs_zero] at h
  have hx : ‖tauE D τ D.host.xi0‖ ≠ 0 :=
    norm_ne_zero_iff.2 ((map_ne_zero (tauE D τ)).2 (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D))
  have hm : ‖tauE D τ μ'‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero (tauE D τ)).2 hsk.1)
  exact (div_ne_zero hx hm) h.symm

end PositivityTheory.Rg.Sw.Glob.RhoH
