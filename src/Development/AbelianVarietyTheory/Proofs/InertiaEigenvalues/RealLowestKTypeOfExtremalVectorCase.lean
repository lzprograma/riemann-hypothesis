module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HolomorphicLowestType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolShapeOfOverK
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionEqZeroOfMeanSquareZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDiscreteSeriesLowestKTypeSmoothIrredu
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilGramSignature

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.RealLowRed

open Formalism.IndefR.FWT

variable {D : D7} {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ}

theorem integrable_star_mul (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T')} {𝓕 : Set (WO S T')} (h1 : μ 𝓕 = 1)
    {f g : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) :
    Integrable (fun w => star (f w) * g w) (μ.restrict 𝓕) := by
  haveI : BorelSpace (WO S T') := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  obtain ⟨C, hC⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hf
  obtain ⟨C', hC'⟩ := GlobalTheory.ThetaSchurBdd.exists_bound hψ hg
  refine Integrable.of_bound (hf.cont.star.mul hg.cont).aestronglyMeasurable (C * C')
    (Filter.Eventually.of_forall fun w => ?_)
  rw [norm_mul, norm_star]
  exact mul_le_mul (hC w) (hC' w) (norm_nonneg _) ((norm_nonneg _).trans (hC w))

theorem thetaInner_add_right (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T')} {𝓕 : Set (WO S T')} (h1 : μ 𝓕 = 1)
    {f g h : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) (hh : IsThetaFunO ψ S T' h) :
    thetaIP μ 𝓕 f (g + h) = thetaIP μ 𝓕 f g + thetaIP μ 𝓕 f h := by
  unfold thetaIP
  rw [← integral_add (integrable_star_mul hψ h1 hf hg) (integrable_star_mul hψ h1 hf hh)]
  congr 1
  funext w
  simp [mul_add]

theorem thetaInner_add_left (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T')} {𝓕 : Set (WO S T')} (h1 : μ 𝓕 = 1)
    {f g h : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) (hh : IsThetaFunO ψ S T' h) :
    thetaIP μ 𝓕 (f + g) h = thetaIP μ 𝓕 f h + thetaIP μ 𝓕 g h := by
  unfold thetaIP
  rw [← integral_add (integrable_star_mul hψ h1 hf hh) (integrable_star_mul hψ h1 hg hh)]
  congr 1
  funext w
  simp [add_mul]

end GlobalTheory.RawLift.RealLowRed

namespace GlobalTheory.RawLift.RealLowRed

open Formalism.IndefR.FWT

variable {D : D7}

def offReal (W : HSp D) : Submodule ℂ (GA D W → ℂ) where
  carrier := {f | ∀ g ∈ GinfC W, f g = 0}
  add_mem' := fun {a b} ha hb g hg => by
    show a g + b g = 0
    rw [ha g hg, hb g hg, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c f hf g hg => by
    show c • f g = 0
    rw [hf g hg, smul_zero]

end GlobalTheory.RawLift.RealLowRed

end
