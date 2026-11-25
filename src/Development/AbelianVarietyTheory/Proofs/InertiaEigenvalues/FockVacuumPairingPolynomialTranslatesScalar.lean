module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientRealPlaceTwoVacua
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormIntegralStarMulSqLeMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFiniteHeisenbergFockVacuumThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtYAndItYOfPair
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVecto
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.VacPairSchur


variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem pT_heisO (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) {w : WO S T}
    (hw : w.map (infPart D) = 0) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T w f) P = heisO ψ S T w (pureTensorO ψ θ S T sS sT BS BT f P) := by
  have h := (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) (GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T w)
    (fun k g _ => ⟨trivial, ?_⟩) f trivial P).2
  · exact h.symm
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll, aPlus, crea]
    rw [map_smul, map_sub, map_smul]
    show _ • (heisO ψ S T w (Formalism.IndefR.Datum.dRho _ _ _ _ _) - _ • heisO ψ S T w (Formalism.IndefR.Datum.dRho _ _ _ _ _)) = _
    rw [GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hw, GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hw]
    rfl

alias thetaIP_eq_ipO := _root_.GlobalTheory.VacSchurFin.thetaIP_eq_ipO

theorem thetaInner_heisenberg (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcv : IsCovolOne (ratL T S) μ 𝓕) {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b)
    (w : WO S T) : thetaIP μ 𝓕 (heisO ψ S T w a) (heisO ψ S T w b) = thetaIP μ 𝓕 a b := by
  rw [thetaIP_eq_ipO, thetaIP_eq_ipO, GlobalTheory.Size.ipO_heisO hψ hcv.1 hcv.2.1 hb ha]

theorem pT_lin (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (a : ℂ) {f f' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (a • f + f') P =
      a • pureTensorO ψ θ S T sS sT BS BT f P + pureTensorO ψ θ S T sS sT BS BT f' P :=
  GlobalTheory.VacCoefAtPlace.pure_lin (P := IsThetaFunO ψ S T) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h)
    (fun _ b _ _ h h' => by
      simp only [aPlusAll]
      rw [GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (GlobalTheory.OrientedHeis.theta_smul b h) h',
        GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ b h]) a hf hf' P

theorem onb_min {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    IsONBasis G s B (min p k) := by
  obtain ⟨ε, h1, h2, h3⟩ := h
  refine ⟨ε, fun a => ?_, h2, h3⟩
  rcases h1 a with ⟨e, ha⟩ | ⟨e, ha⟩
  · exact Or.inl ⟨e, lt_min ha a.2⟩
  · exact Or.inr ⟨e, (min_le_left _ _).trans ha⟩

theorem cs (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcv : IsCovolOne (ratL T S) μ 𝓕) {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) :
    ‖thetaIP μ 𝓕 a b‖ ^ 2 ≤ (thetaIP μ 𝓕 a a).re * (thetaIP μ 𝓕 b b).re := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have ii : ∀ {c : WO S T → ℂ}, IsThetaFunO ψ S T c → Integrable (fun x => star (c x) * c x) (μ.restrict 𝓕) :=
    fun {c} hc => (GlobalTheory.Size.integrableOn_mul_conj hψ hcv.1 hcv.2.1 hc hc).congr
      (ae_of_all _ fun x => mul_comm _ _)
  exact GlobalTheory.norm_integral_star_mul_sq_le (μ.restrict 𝓕) a b ha.cont.aestronglyMeasurable
    hb.cont.aestronglyMeasurable (ii ha) (ii hb)

end GlobalTheory.VacPairSchur
