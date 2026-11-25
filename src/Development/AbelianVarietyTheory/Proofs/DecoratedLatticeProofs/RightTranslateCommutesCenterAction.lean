module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
public import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

@[expose] public section

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)

namespace GlobalTheory.RegSch.CentreRight

open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.PointAtPlaceHom
open Formalism.MainNotions.StandardLattice (infMat)

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem rTr_mem_fin {u : GA D V} (hu : u ∈ GfC V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : rTr V u φ ∈ SmFun θ V := by
  intro n τs Xs hX g
  have := hφ n τs Xs hX (g * u)
  convert this using 2 with t
  unfold rTr
  rw [mul_assoc, mul_assoc, comm_of_mem V (list_prod_mem fun a ha => ?_) hu]
  obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
  exact atTau_mem V _ _

theorem rTr_mul (u a : GA D V) (φ : GA D V → ℂ) : rTr V (u * a) φ = rTr V u (rTr V a φ) := by
  funext g
  simp only [rTr, mul_assoc]

theorem decomp (hθ : IsInfFam θ) (x : GA D V) : ∃ u ∈ GfC V, ∃ a, IsRealPt θ a ∧ x = u * a := by
  obtain ⟨u, hu, a, ha, e⟩ := Formalism.IndefR.TopMult.ga_decomp x
  exact ⟨u, hu, a, ⟨ha, GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V a⟩, e⟩

theorem rTr_mem_all (hθ : IsInfFam θ) (x : GA D V) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) : rTr V x φ ∈ SmFun θ V := by
  obtain ⟨u, hu, a, ha, rfl⟩ := decomp hθ x
  rw [rTr_mul]
  exact rTr_mem_fin hu (rTr_mem hθ ha hφ)

theorem gelf_rTr_all (hθ : IsInfFam θ) (x : GA D V) (τ : D.what₂.Tau) (k : ℕ) {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) :
    gelf θ V τ k (rTr V x φ) = rTr V x (gelf θ V τ k φ) := by
  obtain ⟨u, hu, a, ha, rfl⟩ := decomp hθ x
  rw [rTr_mul, rTr_mul, GlobalTheory.Mem.FinTranslate.gelf_rTr hu, gelf_rTr hθ ha τ k hφ]

end GlobalTheory.RegSch.CentreRight

end
