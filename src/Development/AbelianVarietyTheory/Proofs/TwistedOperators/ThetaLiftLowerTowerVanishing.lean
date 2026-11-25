module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LoweredSignatureVanishing
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RapidDecayLift
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameExistsSignCompat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftCuspFormAutomorphicSmoothModerateGrowth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOfVanishOnFock

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.ChainFr GlobalTheory.Size GlobalTheory.Grow GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift
open scoped ENNReal NNReal

namespace GlobalTheory.LowVanishObj

variable {D : D7}

section Kernel

variable {V W : HSp D} (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (g : GA D V) (h : GA D W)

theorem thetaKO_zero : thetaKO ω g h 0 = 0 := by
  simp [thetaKO]

theorem thetaKO_add (f f' : WO V W → ℂ) : thetaKO ω g h (f + f') = thetaKO ω g h f + thetaKO ω g h f' := by
  simp [thetaKO]

theorem thetaKO_sub (f f' : WO V W → ℂ) : thetaKO ω g h (f - f') = thetaKO ω g h f - thetaKO ω g h f' := by
  simp [thetaKO]

theorem thetaKO_smul (c : ℂ) (f : WO V W → ℂ) : thetaKO ω g h (c • f) = c * thetaKO ω g h f := by
  simp [thetaKO]

end Kernel

theorem multT_apply_cusp {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S) (J : Set (GA D W))
    (χ : GA D W → ℂ) (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) :
    IsAutFunSm θ W (F v) ∧ IsCuspFun W (F v) := by
  apply _root_.GlobalTheory.PairLift.LowAllPf.multT_apply_smooth_cusp <;> assumption

theorem liftInt_span_eq_zero {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {Φ : GA D W → ℂ}
    (hI : ∀ f, IsThetaFunO ψ V W f → ∀ x, IntegrableOn (fun h => thetaKO ω x h f * Φ h) 𝓕 ν)
    {s : Set (WO V W → ℂ)} (hs : ∀ g ∈ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0) :
    ∀ g ∈ Submodule.span ℂ s, IsThetaFunO ψ V W g ∧ Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 := by
  apply _root_.GlobalTheory.PairLift.LowAllPf.liftInt_span_zero <;> assumption

theorem liftInt_eq_zero_of_approx {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)}
    {cls : (GA D W → ℂ) → Prop} (hL : LiftLaws θ ψ ω ν 𝓕 cls) {Φ : GA D W → ℂ} (hΦ : cls Φ)
    {μ : Measure (WO V W)} {𝓓 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓓 : IsAddFundamentalDomain (ratL W V) 𝓓 μ) {U : AddSubgroup (WO V W)} (hU : IsOpen (U : Set (WO V W)))
    {f : WO V W → ℂ} (hf : f ∈ GlobalTheory.Size.thetaLevel ψ V W U)
    (happ : ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ GlobalTheory.Size.thetaLevel ψ V W U,
      Lift.liftInt ν 𝓕 (thetaKO ω) g Φ = 0 ∧ sobO ψ θ μ 𝓓 d (f - g) < δ) :
    Lift.liftInt ν 𝓕 (thetaKO ω) f Φ = 0 := by
  apply _root_.GlobalTheory.PairLift.LowAllPf.liftInt_zero_of_approx <;> assumption

theorem lowVanish_obj : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.LowVanish D := by
  intro h1 h2 h3 D k i V' W M' θ ψ hθ hk hi hsig ω' hω' ν 𝓕 hν h𝓕 J χ F hF v f' hf'
  obtain ⟨χS, χT, hW, hexp⟩ := hω'
  have hLaws := GlobalTheory.Chain.LiftReg.liftProps_obj h3 D V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hcv := multT_apply_cusp θ M' J χ F hF v
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').1
  obtain ⟨μ, 𝓓, hcov⟩ := GlobalTheory.Size.exists_isCovolOne V' W
  have hstd : IsStdChar D ψ (-1) := hW.std
  obtain ⟨U, hU, hfU, happ⟩ :=
    GlobalTheory.FockDensity.fockDense D V' W A (Fr.ofModel M') θ ψ hstd hθ μ 𝓓 hcov f' hf'
  have hint : ∀ f, IsThetaFunO ψ V' W f → ∀ x, IntegrableOn (fun h => thetaKO ω' x h f * F v h) 𝓕 ν :=
    fun f hf x => by simpa [rTr] using hLaws.integ f (F v) hf hcv x 1
  refine liftInt_eq_zero_of_approx hLaws hcv (μ := μ) (𝓓 := 𝓓) hcov.1 hcov.2.1 hU hfU ?_
  intro d δ hδ
  obtain ⟨g, hg, hgU, hsm⟩ := happ d δ hδ
  refine ⟨g, hgU, ?_, hsm⟩
  refine (liftInt_span_eq_zero hint ?_ g hg).2
  rintro _ ⟨f₀, P, hvac, -, rfl⟩
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hstd hθ A.cart A.onb (Fr.ofModel M').cart
      (Fr.ofModel M').onb hvac.1 P
  · exact GlobalTheory.LowerMembers.lowVanishFock h1 h2 h3 D k i V' W M' θ ψ hθ hk hi hsig ω' ⟨χS, χT, hW, hexp⟩
      ν 𝓕 hν h𝓕 J χ F hF v A f₀ hvac P

end GlobalTheory.LowVanishObj

end
