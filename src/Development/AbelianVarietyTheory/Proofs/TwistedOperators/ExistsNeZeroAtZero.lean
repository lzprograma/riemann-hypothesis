module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumUniqueness
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTwistHeckeCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumUniqueOnThetaFunctions
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.WeilDetermined

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem om_om_inv (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p (om p⁻¹ f) = f :=
  GlobalTheory.WeilUniq.om_om_inv om p f

theorem om_inv_om (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (p : GA D S × GA D T) (f : WO S T → ℂ) :
    om p⁻¹ (om p f) = f :=
  GlobalTheory.WeilUniq.om_inv_om om p f

theorem exists_scalar (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') (p : GA D S × GA D T) :
    ∃ c : Circle, ∀ f, IsThetaFunO ψ S T f → om p f = (c : ℂ) • om' p f :=
  GlobalTheory.WeilUniq.exists_scalar H H' p

theorem exists_ne_zero_at_zero (hψ : IsStdChar D ψ (-1)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) :
    ∃ f₀, IsThetaFunO ψ S T f₀ ∧ f₀ 0 ≠ 0 :=
  GlobalTheory.WeilUniq.exists_ne_zero_at_zero hψ hf h0

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  GlobalTheory.WeilUniq.exists_isDetAt he V g

theorem suppAt_one (e : AE D) (V : HSp D) : SuppAt e V 1 :=
  GlobalTheory.WeilUniq.suppAt_one e V

theorem scalar_split (H : IsWeilDatumO ψ S T χS χT om) (H' : IsWeilDatumO ψ S T χS χT om') {e : AE D}
    (he : IsSplitIdem D e) {g : GA D S} {h : GA D T} (hg : SuppAt e S g) (hh : SuppAt e T h) {c : Circle}
    (hc : ∀ f, IsThetaFunO ψ S T f → om (g, h) f = (c : ℂ) • om' (g, h) f) : c = 1 :=
  GlobalTheory.WeilUniq.scalar_split H H' he hg hh hc

theorem agree_on_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om om' : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS χT om' → ∀ p f, IsThetaFunO ψ S T f → om p f = om' p f :=
  GlobalTheory.WeilUniq.weilDatum_unique

theorem hecke_of_mul {χ ξ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (h : IsHeckeChar D (χ * ξ)) :
    IsHeckeChar D ξ := by
  have := GlobalTheory.WeilChange.hecke_mul (GlobalTheory.WeilChange.hecke_inv hχ) h
  rwa [inv_mul_cancel_left] at this

theorem exists_isTildeDet (V : HSp D) {ξ : (AE D)ˣ →* Circle} (hξ : IsHeckeChar D ξ)
    (h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.TrivOnF D ξ) (g : GA D V) :
    ∃ x, IsDetRoot V g x ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.IsTildeDet V ξ g (ξ x) := by
  obtain ⟨a, aval, -⟩ := GlobalTheory.Member.exists_muVal D V ξ hξ h0
  obtain ⟨x, hx⟩ := aval.1 g
  refine ⟨x, hx, ⟨x, hx⟩, fun y hy => Circle.ext ?_⟩
  rw [← aval.2 g x hx, ← aval.2 g y hy]

theorem weilDatumTwist (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.WeilDatumTwist D := by
  intro ψ S T χS χT ξ ξ' om om' h0 h0' H H' g h
  have hξ := hecke_of_mul H.hecS H'.hecS
  have hξ' := hecke_of_mul H.hecT H'.hecT
  obtain ⟨om'', H'', hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ H.std S T χS χT ξ ξ' om H hξ hξ'
    ⟨H.resS.1, fun η _ a => by rw [h0 a, pow_zero]⟩ ⟨H.resS.1, fun η _ a => by rw [h0' a, pow_zero]⟩
  obtain ⟨x, hx, ha⟩ := exists_isTildeDet S hξ' h0' g
  obtain ⟨y, hy, hb⟩ := exists_isTildeDet T hξ h0 h
  refine ⟨ξ' x, ξ y, ha, hb, fun f hf => ?_⟩
  rw [agree_on_theta D ψ H.std S T _ _ om' om'' H' H'' (g, h) f hf, hv g h x y hx hy, LinearMap.smul_apply]

theorem weilDatumDetermined (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumUniquenessCriterion.WeilDatumDetermined D :=
  ⟨(weilDatumTwist D).unique, weilDatumTwist D⟩

end GlobalTheory.WeilDetermined
